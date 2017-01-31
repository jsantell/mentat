// Copyright 2016 Mozilla
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use
// this file except in compliance with the License. You may obtain a copy of the
// License at http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software distributed
// under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

use std::fmt::{Display, Formatter};

/// A simplification of Clojure's Symbol.
#[derive(Clone,Debug,Eq,Hash,Ord,PartialOrd,PartialEq)]
pub struct PlainSymbol(pub String);

#[derive(Clone,Debug,Eq,Hash,Ord,PartialOrd,PartialEq)]
pub struct NamespacedSymbol {
    // We derive PartialOrd, which implements a lexicographic based
    // on the order of members, so put namespace first.
    pub namespace: String,
    pub name: String,
}

/// A keyword is a symbol, optionally with a namespace, that prints with a leading colon.
/// This concept is imported from Clojure, as it features in EDN and the query
/// syntax that we use.
///
/// Clojure's constraints are looser than ours, allowing empty namespaces or
/// names:
///
/// ```clojure
/// user=> (keyword "" "")
/// :/
/// user=> (keyword "foo" "")
/// :foo/
/// user=> (keyword "" "bar")
/// :/bar
/// ```
///
/// We think that's nonsense, so we only allow keywords like `:bar` and `:foo/bar`,
/// with both namespace and main parts containing no whitespace and no colon or slash:
///
/// ```rust
/// # use edn::symbols::Keyword;
/// # use edn::symbols::NamespacedKeyword;
/// let bar     = Keyword::new("bar");                         // :bar
/// let foo_bar = NamespacedKeyword::new("foo", "bar");        // :foo/bar
/// assert_eq!("bar", bar.0);
/// assert_eq!("bar", foo_bar.name);
/// assert_eq!("foo", foo_bar.namespace);
/// ```
///
/// If you're not sure whether your input is well-formed, you should use a
/// parser or a reader function first to validate. TODO: implement `read`.
///
/// Callers are expected to follow these rules:
/// http://www.clojure.org/reference/reader#_symbols
///
/// Future: fast equality (interning?) for keywords.
///
#[derive(Clone,Debug,Eq,Hash,Ord,PartialOrd,PartialEq)]
pub struct Keyword(pub String);

#[derive(Clone,Debug,Eq,Hash,Ord,PartialOrd,PartialEq)]
pub struct NamespacedKeyword {
    // We derive PartialOrd, which implements a lexicographic based
    // on the order of members, so put namespace first.
    pub namespace: String,
    pub name: String,
}

impl PlainSymbol {
    pub fn new<T>(name: T) -> Self where T: Into<String> {
        let n = name.into();
        assert!(!n.is_empty(), "Symbols cannot be unnamed.");

        PlainSymbol(n)
    }

    /// Return the name of the symbol without any leading '?' or '$'.
    ///
    /// ```rust
    /// # use edn::symbols::PlainSymbol;
    /// assert_eq!("foo", PlainSymbol::new("?foo").plain_name());
    /// assert_eq!("foo", PlainSymbol::new("$foo").plain_name());
    /// assert_eq!("!foo", PlainSymbol::new("!foo").plain_name());
    /// ```
    pub fn plain_name(&self) -> &str {
        if self.is_src_symbol() || self.is_var_symbol() {
            &self.0[1..]
        } else {
            &self.0
        }
    }

    #[inline]
    pub fn is_var_symbol(&self) -> bool {
        self.0.starts_with('?')
    }

    #[inline]
    pub fn is_src_symbol(&self) -> bool {
        self.0.starts_with('$')
    }
}

impl NamespacedSymbol {
    pub fn new<T>(namespace: T, name: T) -> Self where T: Into<String> {
        let n = name.into();
        let ns = namespace.into();

        assert!(!n.is_empty(), "Symbols cannot be unnamed.");
        assert!(!ns.is_empty(), "Symbols cannot have an empty non-null namespace.");

        NamespacedSymbol { name: n, namespace: ns }
    }
}

impl Keyword {
    pub fn new<T>(name: T) -> Self where T: Into<String> {
        let n = name.into();
        assert!(!n.is_empty(), "Keywords cannot be unnamed.");

        Keyword(n)
    }
}

impl NamespacedKeyword {
    pub fn new<T>(namespace: T, name: T) -> Self where T: Into<String> {
        let n = name.into();
        let ns = namespace.into();
        assert!(!n.is_empty(), "Keywords cannot be unnamed.");
        assert!(!ns.is_empty(), "Keywords cannot have an empty non-null namespace.");

        // TODO: debug asserts to ensure that neither field matches [ :/].
        NamespacedKeyword { name: n, namespace: ns }
    }
}

//
// Note that we don't currently do any escaping.
//

impl Display for PlainSymbol {
    /// Print the symbol in EDN format.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use edn::symbols::PlainSymbol;
    /// assert_eq!("baz", PlainSymbol::new("baz").to_string());
    /// ```
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for NamespacedSymbol {
    /// Print the symbol in EDN format.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use edn::symbols::NamespacedSymbol;
    /// assert_eq!("bar/baz", NamespacedSymbol::new("bar", "baz").to_string());
    /// ```
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        write!(f, "{}/{}", self.namespace, self.name)
    }
}

impl Display for Keyword {
    /// Print the keyword in EDN format.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use edn::symbols::Keyword;
    /// assert_eq!(":baz", Keyword::new("baz").to_string());
    /// ```
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        write!(f, ":{}", self.0)
    }
}

impl Display for NamespacedKeyword {
    /// Print the keyword in EDN format.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use edn::symbols::NamespacedKeyword;
    /// assert_eq!(":bar/baz", NamespacedKeyword::new("bar", "baz").to_string());
    /// ```
    fn fmt(&self, f: &mut Formatter) -> ::std::fmt::Result {
        write!(f, ":{}/{}", self.namespace, self.name)
    }
}
