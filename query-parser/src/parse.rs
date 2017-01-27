// Copyright 2016 Mozilla
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use
// this file except in compliance with the License. You may obtain a copy of the
// License at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software distributed
// under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

extern crate combine;
extern crate edn;
extern crate mentat_query;

use self::combine::{eof, many1, optional, parser, satisfy_map, token, Parser, ParseResult, Stream};
use self::combine::combinator::{Expected, FnParser, choice, try};
use self::edn::Value::PlainSymbol;
use self::mentat_query::{
    Element,
    FindSpec,
    NonIntegerConstant,
    Pattern,
    PatternNonValuePlace,
    PatternValuePlace,
    SrcVar,
    Variable,
    WhereClause,
};

use super::error::{FindParseError, FindParseResult};

pub struct Query<I>(::std::marker::PhantomData<fn(I) -> I>);
pub struct Where<I>(::std::marker::PhantomData<fn(I) -> I>);
pub struct Find<I>(::std::marker::PhantomData<fn(I) -> I>);

// Nothing about this is specific to the type of parser.
type ResultParser<O, I> = Expected<FnParser<I, fn(I) -> ParseResult<O, I>>>;

fn fn_parser<O, I>(f: fn(I) -> ParseResult<O, I>, err: &'static str) -> ResultParser<O, I>
    where I: Stream<Item = edn::Value>
{
    parser(f).expected(err)
}

/// `satisfy_unwrap!` makes it a little easier to implement a `satisfy_map`
/// body that matches a particular `Value` enum case, otherwise returning `None`.
macro_rules! satisfy_unwrap {
    ( $cas: path, $var: ident, $body: block ) => {
        satisfy_map(|x: edn::Value| if let $cas($var) = x $body else { None })
    }
}

/// Generate a `satisfy_map` expression that matches a `PlainSymbol`
/// value with the given name.
///
/// We do this rather than using `combine::token` so that we don't
/// need to allocate a new `String` inside a `PlainSymbol` inside a `Value`
/// just to match input.
macro_rules! matches_plain_symbol {
    ($name: expr, $input: ident) => {
        satisfy_map(|x: edn::Value| {
            if let PlainSymbol(ref s) = x {
                if s.0.as_str() == $name {
                    return Some(());
                }
            }
            return None;
        }).parse_stream($input)
    }
}

trait FromValue<T> {
    fn from_value(edn::Value) -> Option<T>;
}

impl FromValue<PatternNonValuePlace> for PatternNonValuePlace {
    fn from_value(v: edn::Value) -> Option<PatternNonValuePlace> {
        match v {
            edn::Value::Integer(x) => if x >= 0 {
                Some(PatternNonValuePlace::Entid(x as u64))
            } else {
                None
            },
            edn::Value::PlainSymbol(x) => if x.0.as_str() == "_" {
                Some(PatternNonValuePlace::Placeholder)
            } else if x.is_var_symbol() {
                Some(PatternNonValuePlace::Variable(Variable(x)))
            } else {
                None
            },
            edn::Value::NamespacedKeyword(x) =>
                Some(PatternNonValuePlace::Ident(x)),
            _ => None,
        }
    }
}

impl FromValue<PatternValuePlace> for PatternValuePlace {
    fn from_value(v: edn::Value) -> Option<PatternValuePlace> {
        match v {
            edn::Value::Integer(x) => Some(PatternValuePlace::EntidOrInteger(x)),
            edn::Value::PlainSymbol(x) => if x.0.as_str() == "_" {
                Some(PatternValuePlace::Placeholder)
            } else if x.is_var_symbol() {
                Some(PatternValuePlace::Variable(Variable(x)))
            } else {
                None
            },
            edn::Value::NamespacedKeyword(x) =>
                Some(PatternValuePlace::IdentOrKeyword(x)),
            edn::Value::Boolean(x) => Some(PatternValuePlace::Constant(NonIntegerConstant::Boolean(x))),
            edn::Value::Float(x) => Some(PatternValuePlace::Constant(NonIntegerConstant::Float(x))),
            edn::Value::BigInteger(x) => Some(PatternValuePlace::Constant(NonIntegerConstant::BigInteger(x))),
            edn::Value::Text(x) => Some(PatternValuePlace::Constant(NonIntegerConstant::Text(x))),
            _ => None,
        }
    }
}

impl<I> Query<I>
    where I: Stream<Item = edn::Value>
{
    fn source_var() -> ResultParser<SrcVar, I> {
        fn_parser(Query::<I>::source_var_, "source_var")
    }

    fn source_var_(input: I) -> ParseResult<SrcVar, I> {
        satisfy_map(SrcVar::from_value).parse_stream(input)
    }

    fn variable() -> ResultParser<Variable, I> {
        fn_parser(Query::<I>::variable_, "variable")
    }

    fn variable_(input: I) -> ParseResult<Variable, I> {
        satisfy_map(|x: edn::Value| super::util::value_to_variable(&x)).parse_stream(input)
    }

    fn to_parsed_value<T>(r: ParseResult<T, I>) -> Option<T> {
        r.ok().map(|x| x.0)
    }
}

impl<I> Where<I>
    where I: Stream<Item = edn::Value>
{
    fn pattern_value_place() -> ResultParser<PatternValuePlace, I> {
        fn_parser(Where::<I>::pattern_value_place_, "pattern_value_place")
    }

    fn pattern_value_place_(input: I) -> ParseResult<PatternValuePlace, I> {
        satisfy_map(|x: edn::Value| PatternValuePlace::from_value(x)).parse_stream(input)
    }

    fn pattern_non_value_place() -> ResultParser<PatternNonValuePlace, I> {
        fn_parser(Where::<I>::pattern_non_value_place_, "pattern_non_value_place")
    }

    fn pattern_non_value_place_(input: I) -> ParseResult<PatternNonValuePlace, I> {
        satisfy_map(|x: edn::Value| PatternNonValuePlace::from_value(x)).parse_stream(input)
    }

    fn pattern() -> ResultParser<Pattern, I> {
        fn_parser(Where::<I>::pattern_, "pattern")
    }

    fn pattern_(input: I) -> ParseResult<Pattern, I> {
        satisfy_unwrap!(edn::Value::Vector, y, {
            // While *technically* Datomic allows you to have a query like:
            // [:find … :where [[?x]]]
            // We don't -- we require at list e, a.
            let mut p =
            (optional(Query::source_var()),                 // src
             Where::pattern_non_value_place(),              // e
             Where::pattern_non_value_place(),              // a
             optional(Where::pattern_value_place()),        // v
             optional(Where::pattern_non_value_place()),    // tx
             eof())
                .map(|(src, e, a, v, tx, _)| {
                     let v = v.unwrap_or(PatternValuePlace::Placeholder);
                     let tx = tx.unwrap_or(PatternNonValuePlace::Placeholder);
                     Pattern {
                         source: src,
                         entity: e,
                         attribute: a,
                         value: v,
                         tx: tx,
                     }
                });
            Query::to_parsed_value(p.parse_lazy(&y[..]).into())
        })
        .parse_stream(input)
    }
}

impl<I> Find<I>
    where I: Stream<Item = edn::Value>
{
    fn period() -> ResultParser<(), I> {
        fn_parser(Find::<I>::period_, "period")
    }

    fn period_(input: I) -> ParseResult<(), I> {
        matches_plain_symbol!(".", input)
    }

    fn ellipsis() -> ResultParser<(), I> {
        fn_parser(Find::<I>::ellipsis_, "ellipsis")
    }

    fn ellipsis_(input: I) -> ParseResult<(), I> {
        matches_plain_symbol!("...", input)
    }

    fn find_scalar() -> ResultParser<FindSpec, I> {
        fn_parser(Find::<I>::find_scalar_, "find_scalar")
    }

    fn find_scalar_(input: I) -> ParseResult<FindSpec, I> {
        (Query::variable(), Find::period(), eof())
            .map(|(var, _, _)| FindSpec::FindScalar(Element::Variable(var)))
            .parse_stream(input)
    }

    fn find_coll() -> ResultParser<FindSpec, I> {
        fn_parser(Find::<I>::find_coll_, "find_coll")
    }

    fn find_coll_(input: I) -> ParseResult<FindSpec, I> {
        satisfy_unwrap!(edn::Value::Vector, y, {
                let mut p = (Query::variable(), Find::ellipsis(), eof())
                    .map(|(var, _, _)| FindSpec::FindColl(Element::Variable(var)));
                let r: ParseResult<FindSpec, _> = p.parse_lazy(&y[..]).into();
                Query::to_parsed_value(r)
            })
            .parse_stream(input)
    }

    fn elements() -> ResultParser<Vec<Element>, I> {
        fn_parser(Find::<I>::elements_, "elements")
    }

    fn elements_(input: I) -> ParseResult<Vec<Element>, I> {
        (many1::<Vec<Variable>, _>(Query::variable()), eof())
            .map(|(vars, _)| {
                vars.into_iter()
                    .map(Element::Variable)
                    .collect()
            })
            .parse_stream(input)
    }

    fn find_rel() -> ResultParser<FindSpec, I> {
        fn_parser(Find::<I>::find_rel_, "find_rel")
    }

    fn find_rel_(input: I) -> ParseResult<FindSpec, I> {
        Find::elements().map(FindSpec::FindRel).parse_stream(input)
    }

    fn find_tuple() -> ResultParser<FindSpec, I> {
        fn_parser(Find::<I>::find_tuple_, "find_tuple")
    }

    fn find_tuple_(input: I) -> ParseResult<FindSpec, I> {
        satisfy_unwrap!(edn::Value::Vector, y, {
                let r: ParseResult<FindSpec, _> =
                    Find::elements().map(FindSpec::FindTuple).parse_lazy(&y[..]).into();
                Query::to_parsed_value(r)
            })
            .parse_stream(input)
    }

    fn find() -> ResultParser<FindSpec, I> {
        fn_parser(Find::<I>::find_, "find")
    }

    fn find_(input: I) -> ParseResult<FindSpec, I> {
        // Any one of the four specs might apply, so we combine them with `choice`.
        // Our parsers consume input, so we need to wrap them in `try` so that they
        // operate independently.
        choice::<[&mut Parser<Input = I, Output = FindSpec>; 4],
                 _>([&mut try(Find::find_scalar()),
                     &mut try(Find::find_coll()),
                     &mut try(Find::find_tuple()),
                     &mut try(Find::find_rel())])
            .parse_stream(input)
    }
}

// Parse a sequence of values into one of four find specs.
//
// `:find` must be an array of plain var symbols (?foo), pull expressions, and aggregates.
// For now we only support variables and the annotations necessary to declare which
// flavor of :find we want:
//
//
//     `?x ?y ?z  `     = FindRel
//     `[?x ...]  `     = FindColl
//     `?x .      `     = FindScalar
//     `[?x ?y ?z]`     = FindTuple
//
pub fn find_seq_to_find_spec(find: &[edn::Value]) -> FindParseResult {
    Find::find()
        .parse(find)
        .map(|x| x.0)
        .map_err(|_| FindParseError::Err)
}

#[cfg(test)]
mod test {
    extern crate combine;
    extern crate edn;
    extern crate mentat_query;
    extern crate ordered_float;

    use self::combine::Parser;
    use self::ordered_float::OrderedFloat;
    use self::mentat_query::{
        Element,
        FindSpec,
        NonIntegerConstant,
        Pattern,
        PatternNonValuePlace,
        PatternValuePlace,
        SrcVar,
        Variable,
    };

    use super::*;

    macro_rules! assert_parses_to {
        ( $parser: path, $input: expr, $expected: expr ) => {{
            let mut par = $parser();
            let result = par.parse(&$input[..]);
            assert_eq!(result, Ok(($expected, &[][..])));
        }}
    }

    #[test]
    fn test_pattern_mixed() {
        let e = edn::PlainSymbol::new("_");
        let a = edn::NamespacedKeyword::new("foo", "bar");
        let v = OrderedFloat(99.9);
        let tx = edn::PlainSymbol::new("?tx");
        let input = [edn::Value::Vector(
            vec!(edn::Value::PlainSymbol(e.clone()),
                 edn::Value::NamespacedKeyword(a.clone()),
                 edn::Value::Float(v.clone()),
                 edn::Value::PlainSymbol(tx.clone())))];
        assert_parses_to!(Where::pattern, input, Pattern {
            source: None,
            entity: PatternNonValuePlace::Placeholder,
            attribute: PatternNonValuePlace::Ident(a),
            value: PatternValuePlace::Constant(NonIntegerConstant::Float(v)),
            tx: PatternNonValuePlace::Variable(Variable(tx)),
        });
    }

    #[test]
    fn test_pattern_vars() {
        let s = edn::PlainSymbol::new("$x");
        let e = edn::PlainSymbol::new("?e");
        let a = edn::PlainSymbol::new("?a");
        let v = edn::PlainSymbol::new("?v");
        let tx = edn::PlainSymbol::new("?tx");
        let input = [edn::Value::Vector(
            vec!(edn::Value::PlainSymbol(s.clone()),
                 edn::Value::PlainSymbol(e.clone()),
                 edn::Value::PlainSymbol(a.clone()),
                 edn::Value::PlainSymbol(v.clone()),
                 edn::Value::PlainSymbol(tx.clone())))];
        assert_parses_to!(Where::pattern, input, Pattern {
            source: Some(SrcVar::NamedSrc("x".to_string())),
            entity: PatternNonValuePlace::Variable(Variable(e)),
            attribute: PatternNonValuePlace::Variable(Variable(a)),
            value: PatternValuePlace::Variable(Variable(v)),
            tx: PatternNonValuePlace::Variable(Variable(tx)),
        });
    }

    #[test]
    fn test_find_sp_variable() {
        let sym = edn::PlainSymbol::new("?x");
        let input = [edn::Value::PlainSymbol(sym.clone())];
        assert_parses_to!(Query::variable, input, Variable(sym));
    }

    #[test]
    fn test_find_scalar() {
        let sym = edn::PlainSymbol::new("?x");
        let period = edn::PlainSymbol::new(".");
        let input = [edn::Value::PlainSymbol(sym.clone()), edn::Value::PlainSymbol(period.clone())];
        assert_parses_to!(Find::find_scalar,
                          input,
                          FindSpec::FindScalar(Element::Variable(Variable(sym))));
    }

    #[test]
    fn test_find_coll() {
        let sym = edn::PlainSymbol::new("?x");
        let period = edn::PlainSymbol::new("...");
        let input = [edn::Value::Vector(vec![edn::Value::PlainSymbol(sym.clone()),
                                             edn::Value::PlainSymbol(period.clone())])];
        assert_parses_to!(Find::find_coll,
                          input,
                          FindSpec::FindColl(Element::Variable(Variable(sym))));
    }

    #[test]
    fn test_find_rel() {
        let vx = edn::PlainSymbol::new("?x");
        let vy = edn::PlainSymbol::new("?y");
        let input = [edn::Value::PlainSymbol(vx.clone()), edn::Value::PlainSymbol(vy.clone())];
        assert_parses_to!(Find::find_rel,
                          input,
                          FindSpec::FindRel(vec![Element::Variable(Variable(vx)),
                                                 Element::Variable(Variable(vy))]));
    }

    #[test]
    fn test_find_tuple() {
        let vx = edn::PlainSymbol::new("?x");
        let vy = edn::PlainSymbol::new("?y");
        let input = [edn::Value::Vector(vec![edn::Value::PlainSymbol(vx.clone()),
                                             edn::Value::PlainSymbol(vy.clone())])];
        assert_parses_to!(Find::find_tuple,
                          input,
                          FindSpec::FindTuple(vec![Element::Variable(Variable(vx)),
                                                   Element::Variable(Variable(vy))]));
    }

    #[test]
    fn test_find_processing() {
        let vx = edn::PlainSymbol::new("?x");
        let vy = edn::PlainSymbol::new("?y");
        let ellipsis = edn::PlainSymbol::new("...");
        let period = edn::PlainSymbol::new(".");

        let scalar = [edn::Value::PlainSymbol(vx.clone()), edn::Value::PlainSymbol(period.clone())];
        let tuple = [edn::Value::Vector(vec![edn::Value::PlainSymbol(vx.clone()),
                                             edn::Value::PlainSymbol(vy.clone())])];
        let coll = [edn::Value::Vector(vec![edn::Value::PlainSymbol(vx.clone()),
                                            edn::Value::PlainSymbol(ellipsis.clone())])];
        let rel = [edn::Value::PlainSymbol(vx.clone()), edn::Value::PlainSymbol(vy.clone())];

        assert_eq!(Ok(FindSpec::FindScalar(Element::Variable(Variable(vx.clone())))),
                   find_seq_to_find_spec(&scalar));
        assert_eq!(Ok(FindSpec::FindTuple(vec![Element::Variable(Variable(vx.clone())),
                                               Element::Variable(Variable(vy.clone()))])),
                   find_seq_to_find_spec(&tuple));
        assert_eq!(Ok(FindSpec::FindColl(Element::Variable(Variable(vx.clone())))),
                   find_seq_to_find_spec(&coll));
        assert_eq!(Ok(FindSpec::FindRel(vec![Element::Variable(Variable(vx.clone())),
                                             Element::Variable(Variable(vy.clone()))])),
                   find_seq_to_find_spec(&rel));
    }
}
