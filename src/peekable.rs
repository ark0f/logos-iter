// Peek logic and tests are taken from core::iter::Peekable
//
// Rust copyright:
// The Rust Project is dual-licensed under Apache 2.0 and MIT
// terms.

use crate::LogosIter;
use logos::{Logos, Source, Span};

/// Peekable version of Logos lexer.
///
/// It's needed because `Iterator::peekable` have no methods like
/// `peek_span()` or `peek_slice()` and so on.
///
/// Methods like `peek_*()` require mutable reference to lexer.
///
/// # Example
/// ```rust
/// use logos::{Lexer, Logos};
/// use logos_iter::LogosIter;
///
/// #[derive(Debug, Logos, PartialEq, Eq)]
/// enum Token {
///     #[error]
///     Error,
///     #[token("foo")]
///     Foo,
///     #[token("bar")]
///     Bar,
/// }
///
/// let mut lexer = Token::lexer("foobar").peekable_lexer();
///
/// assert_eq!(lexer.next(), Some(Token::Foo));
/// assert_eq!(lexer.peek(), Some(&Token::Bar));
/// assert_eq!(lexer.peek_slice(), "bar");
/// assert_eq!(lexer.peek_span(), 3..6);
/// ```
pub struct PeekableLexer<'source, L, T>
where
    L: LogosIter<'source, T>,
    T: Logos<'source>,
{
    pub(crate) lexer: L,
    pub(crate) peeked: Option<Peeked<'source, T>>,
}

pub(crate) struct Peeked<'source, T>
where
    T: Logos<'source>,
{
    token: Option<T>,
    prev_span: Span,
    span: Span,
    remainder: &'source <T::Source as Source>::Slice,
}

impl<'source, T> Clone for Peeked<'source, T>
where
    T: Logos<'source> + Clone,
{
    fn clone(&self) -> Self {
        Self {
            token: self.token.clone(),
            prev_span: self.span.clone(),
            span: self.span.clone(),
            remainder: self.remainder,
        }
    }
}

impl<'source, L, T> PeekableLexer<'source, L, T>
where
    L: LogosIter<'source, T>,
    T: Logos<'source>,
{
    fn peek_impl(&mut self) -> &mut Peeked<'source, T> {
        let lexer = &mut self.lexer;
        self.peeked.get_or_insert_with(|| Peeked {
            prev_span: lexer.span(),
            token: lexer.next(),
            span: lexer.span(),
            remainder: lexer.remainder(),
        })
    }

    pub fn peek(&mut self) -> Option<&T> {
        self.peek_impl().token.as_ref()
    }

    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.peek_impl().token.as_mut()
    }

    pub fn peek_span(&mut self) -> Span {
        self.peek_impl().span.clone()
    }

    pub fn peek_slice(&mut self) -> &'source <T::Source as logos::Source>::Slice {
        let span = self.peek_span();
        // SAFETY: span is in range of source
        unsafe { self.lexer.source().slice_unchecked(span) }
    }

    pub fn peek_remainder(&mut self) -> &'source <T::Source as logos::Source>::Slice {
        self.peek_impl().remainder
    }

    pub fn next_if(&mut self, func: impl FnOnce(&T) -> bool) -> Option<T> {
        let prev_span = self.span();

        match self.next() {
            Some(matched) if func(&matched) => Some(matched),
            other => {
                // Since we called `self.next()`, we consumed `self.peeked`.
                assert!(self.peeked.is_none());
                self.peeked = Some(Peeked {
                    token: other,
                    prev_span,
                    span: self.lexer.span(),
                    remainder: self.lexer.remainder(),
                });
                None
            }
        }
    }

    pub fn next_if_eq<U>(&mut self, expected: &U) -> Option<T>
    where
        T: PartialEq<U>,
    {
        self.next_if(|next| next == expected)
    }
}

impl<'source, L, T> Clone for PeekableLexer<'source, L, T>
where
    L: LogosIter<'source, T> + Clone,
    T: Logos<'source> + Clone,
    T::Extras: Clone,
{
    fn clone(&self) -> Self {
        Self {
            lexer: self.lexer.clone(),
            peeked: self.peeked.clone(),
        }
    }
}

impl<'source, L, T> Iterator for PeekableLexer<'source, L, T>
where
    L: LogosIter<'source, T>,
    T: Logos<'source>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.peeked.take() {
            None => self.lexer.next(),
            Some(Peeked { token, .. }) => token,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let peek_len = match self.peeked {
            Some(Peeked { token: None, .. }) => return (0, Some(0)),
            Some(Peeked { token: Some(_), .. }) => 1,
            None => 0,
        };
        let (lo, hi) = self.lexer.size_hint();
        let lo = lo.saturating_add(peek_len);
        let hi = match hi {
            Some(x) => x.checked_add(peek_len),
            None => None,
        };
        (lo, hi)
    }

    fn count(mut self) -> usize {
        match self.peeked.take() {
            Some(Peeked { token: None, .. }) => 0,
            Some(Peeked { token: Some(_), .. }) => 1 + self.lexer.count(),
            None => self.lexer.count(),
        }
    }

    fn last(mut self) -> Option<T> {
        let peek_opt = match self.peeked.take() {
            Some(Peeked { token: None, .. }) => return None,
            Some(Peeked {
                token: v @ Some(_), ..
            }) => v,
            None => None,
        };
        self.lexer.last().or(peek_opt)
    }

    fn nth(&mut self, n: usize) -> Option<T> {
        match self.peeked.take() {
            Some(Peeked { token: None, .. }) => None,
            Some(Peeked {
                token: v @ Some(_), ..
            }) if n == 0 => v,
            Some(Peeked { token: Some(_), .. }) => self.lexer.nth(n - 1),
            None => self.lexer.nth(n),
        }
    }

    fn fold<Acc, Fold>(self, init: Acc, mut fold: Fold) -> Acc
    where
        Fold: FnMut(Acc, T) -> Acc,
    {
        let acc = match self.peeked {
            Some(Peeked { token: None, .. }) => return init,
            Some(Peeked { token: Some(v), .. }) => fold(init, v),
            None => init,
        };
        self.lexer.fold(acc, fold)
    }
}

impl<'source, L, T> LogosIter<'source, T> for PeekableLexer<'source, L, T>
where
    L: LogosIter<'source, T>,
    T: Logos<'source>,
{
    fn span(&self) -> Span {
        match &self.peeked {
            None => self.lexer.span(),
            Some(Peeked { span, .. }) => span.clone(),
        }
    }

    fn slice(&self) -> &'source <T::Source as logos::Source>::Slice {
        let span = self.span();
        // SAFETY: span is in range of source
        unsafe { self.lexer.source().slice_unchecked(span) }
    }

    fn source(&self) -> &'source T::Source {
        self.lexer.source()
    }

    fn remainder(&self) -> &'source <T::Source as logos::Source>::Slice {
        match &self.peeked {
            None => self.lexer.remainder(),
            Some(Peeked { prev_span, .. }) => {
                let source = self.lexer.source();
                // SAFETY: span is in range of source
                unsafe { source.slice_unchecked(prev_span.end..source.len()) }
            }
        }
    }

    fn bump(&mut self, n: usize) {
        match self.peeked.take() {
            None => self.lexer.bump(n),
            Some(Peeked { span, .. }) => {
                let token_len = span.end - span.start;
                let n = n - token_len;
                self.lexer.bump(n);
            }
        }
    }

    fn extras(&self) -> &T::Extras {
        self.lexer.extras()
    }

    fn extras_mut(&mut self) -> &mut T::Extras {
        self.lexer.extras_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use logos::Lexer;

    #[derive(Debug, Logos, PartialEq, Eq, Copy, Clone)]
    enum Token {
        #[error]
        #[token(" ", logos::skip)]
        Error,
        #[token("0")]
        Zero,
        #[token("1")]
        One,
        #[token("2")]
        Two,
        #[token("3")]
        Three,
        #[token("4")]
        Four,
        #[token("5")]
        Five,
        #[token("heart")]
        Heart,
        #[token("of")]
        Of,
        #[token("gold")]
        Gold,
        #[token("trillian")]
        Trillian,
        #[token("zaphod")]
        Zaphod,
    }

    fn make_it(s: &'static str) -> PeekableLexer<'static, Lexer<'static, Token>, Token> {
        Token::lexer(s).peekable_lexer()
    }

    #[test]
    fn test_lexer_bump() {
        // `heart` 2 spaces `of` 3 spaces `gold`
        const XS: &str = "heart  of   gold";

        // peek and bump
        let mut it = make_it(XS);
        assert_eq!(it.peek(), Some(&Token::Heart));
        it.bump(5);
        assert_eq!(it.peek(), Some(&Token::Of));
        assert_eq!(it.remainder(), "  of   gold");
        assert_eq!(it.next(), Some(Token::Of));
        assert_eq!(it.remainder(), "   gold");

        // bump
        let mut it = make_it(XS);
        it.bump(5);
        assert_eq!(it.remainder(), "  of   gold");
        assert_eq!(it.next(), Some(Token::Of));

        // next and bump
        let mut it = make_it(XS);
        assert_eq!(it.next(), Some(Token::Heart));
        it.bump(4); // `  of`
        assert_eq!(it.remainder(), "   gold");
        assert_eq!(it.next(), Some(Token::Gold));
    }

    #[test]
    fn test_lexer_peekable() {
        const XS: &str = "0 1 2 3 4 5 heart of gold";
        let mut it = make_it(XS);

        assert_eq!(it.remainder(), XS);
        assert_eq!(it.peek().unwrap(), &Token::Zero);
        assert_eq!(it.peek_slice(), "0");
        assert_eq!(it.peek_span(), 0..1);
        assert_eq!(it.peek_remainder(), " 1 2 3 4 5 heart of gold");
        assert_eq!(it.remainder(), XS);
        assert_eq!(it.next().unwrap(), Token::Zero);
        assert_eq!(it.slice(), "0");
        assert_eq!(it.span(), 0..1);
        assert_eq!(it.remainder(), " 1 2 3 4 5 heart of gold");
        assert_eq!(it.next().unwrap(), Token::One);
        assert_eq!(it.slice(), "1");
        assert_eq!(it.span(), 2..3);
        assert_eq!(it.remainder(), " 2 3 4 5 heart of gold");
        assert_eq!(it.next().unwrap(), Token::Two);
        assert_eq!(it.slice(), "2");
        assert_eq!(it.span(), 4..5);
        assert_eq!(it.remainder(), " 3 4 5 heart of gold");
        assert_eq!(it.peek().unwrap(), &Token::Three);
        assert_eq!(it.peek_slice(), "3");
        assert_eq!(it.peek_span(), 6..7);
        assert_eq!(it.peek_remainder(), " 4 5 heart of gold");
        assert_eq!(it.peek().unwrap(), &Token::Three);
        assert_eq!(it.peek_slice(), "3");
        assert_eq!(it.peek_span(), 6..7);
        assert_eq!(it.peek_remainder(), " 4 5 heart of gold");
        assert_eq!(it.next().unwrap(), Token::Three);
        assert_eq!(it.slice(), "3");
        assert_eq!(it.span(), 6..7);
        assert_eq!(it.remainder(), " 4 5 heart of gold");
        assert_eq!(it.next().unwrap(), Token::Four);
        assert_eq!(it.slice(), "4");
        assert_eq!(it.span(), 8..9);
        assert_eq!(it.remainder(), " 5 heart of gold");
        assert_eq!(it.peek().unwrap(), &Token::Five);
        assert_eq!(it.peek_slice(), "5");
        assert_eq!(it.peek_span(), 10..11);
        assert_eq!(it.peek_remainder(), " heart of gold");
        assert_eq!(it.next().unwrap(), Token::Five);
        assert_eq!(it.slice(), "5");
        assert_eq!(it.span(), 10..11);
        assert_eq!(it.remainder(), " heart of gold");
        assert_eq!(it.peek().unwrap(), &Token::Heart);
        assert_eq!(it.peek_slice(), "heart");
        assert_eq!(it.peek_span(), 12..17);
        assert_eq!(it.peek_remainder(), " of gold");
        assert_eq!(it.next().unwrap(), Token::Heart);
        assert_eq!(it.slice(), "heart");
        assert_eq!(it.span(), 12..17);
        assert_eq!(it.remainder(), " of gold");
        assert_eq!(it.peek().unwrap(), &Token::Of);
        assert_eq!(it.peek_slice(), "of");
        assert_eq!(it.peek_span(), 18..20);
        assert_eq!(it.peek_remainder(), " gold");
        assert_eq!(it.next().unwrap(), Token::Of);
        assert_eq!(it.slice(), "of");
        assert_eq!(it.span(), 18..20);
        assert_eq!(it.remainder(), " gold");
        assert_eq!(it.peek().unwrap(), &Token::Gold);
        assert_eq!(it.peek_slice(), "gold");
        assert_eq!(it.peek_span(), 21..25);
        assert_eq!(it.peek_remainder(), "");
        assert_eq!(it.next().unwrap(), Token::Gold);
        assert_eq!(it.slice(), "gold");
        assert_eq!(it.span(), 21..25);
        assert_eq!(it.remainder(), "");
        assert!(it.peek().is_none());
        assert!(it.next().is_none());
    }

    #[test]
    fn test_iterator_peekable_count() {
        const XS: &str = "0 1 2 3 4 5";
        const YS: &str = "1 0";
        const ZS: &str = "";

        let xs = make_it(XS);
        assert_eq!(xs.count(), 6);

        let mut it = make_it(XS);
        assert_eq!(it.peek(), Some(&Token::Zero));
        assert_eq!(it.count(), 6);

        assert_eq!(make_it(YS).count(), 2);

        let mut it = make_it(YS);
        assert_eq!(it.peek(), Some(&Token::One));
        assert_eq!(it.count(), 2);

        assert_eq!(make_it(ZS).count(), 0);

        let mut it = make_it(ZS);
        assert_eq!(it.peek(), None);
    }

    #[allow(clippy::iter_nth_zero)]
    #[test]
    fn test_iterator_peekable_nth() {
        const XS: &str = "0 1 2 3 4 5";
        let mut it = make_it(XS);

        assert_eq!(it.peek(), Some(&Token::Zero));
        assert_eq!(it.nth(0), Some(Token::Zero));
        assert_eq!(it.peek(), Some(&Token::One));
        assert_eq!(it.nth(1), Some(Token::Two));
        assert_eq!(it.peek(), Some(&Token::Three));
        assert_eq!(it.nth(2), Some(Token::Five));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_iterator_peekable_last() {
        const XS: &str = "0 1 2 3 4 5";
        const YS: &str = "0";

        let mut it = make_it(XS);
        assert_eq!(it.peek(), Some(&Token::Zero));
        assert_eq!(it.last(), Some(Token::Five));

        let mut it = make_it(YS);
        assert_eq!(it.peek(), Some(&Token::Zero));
        assert_eq!(it.last(), Some(Token::Zero));

        let mut it = make_it(YS);
        assert_eq!(it.next(), Some(Token::Zero));
        assert_eq!(it.peek(), None);
        assert_eq!(it.last(), None);
    }

    #[test]
    fn test_iterator_peekable_fold() {
        const XS: &str = "0 1 2 3 4 5";

        let mut it = make_it(XS);
        let xs: Vec<_> = it.clone().collect();
        assert_eq!(it.peek(), Some(&Token::Zero));
        let i = it.fold(0, |i, x| {
            assert_eq!(x, xs[i]);
            i + 1
        });
        assert_eq!(i, xs.len());
    }

    #[test]
    fn test_iterator_peekable_next_if_eq() {
        // first, try on references
        const XS: &str = "heart of gold";
        let mut it = make_it(XS);
        // try before `peek()`
        assert_eq!(it.next_if_eq(&Token::Trillian), None);
        assert_eq!(it.next_if_eq(&Token::Heart), Some(Token::Heart));
        // try after peek()
        assert_eq!(it.peek(), Some(&Token::Of));
        assert_eq!(it.next_if_eq(&Token::Of), Some(Token::Of));
        assert_eq!(it.next_if_eq(&Token::Zaphod), None);
        // make sure `next()` still behaves
        assert_eq!(it.next(), Some(Token::Gold));
    }

    #[test]
    fn test_iterator_peekable_mut() {
        const XS: &str = "1 2 3";
        let mut it = make_it(XS);
        if let Some(p) = it.peek_mut() {
            if *p == Token::One {
                *p = Token::Five;
            }
        }
        assert_eq!(it.collect::<Vec<_>>(), vec![
            Token::Five,
            Token::Two,
            Token::Three
        ]);
    }

    /*

    #[test]
        fn test_iterator_peekable_remember_peek_none_1() {
            // Check that the loop using .peek() terminates
            let lexer = make_it("1 2 3");
            let data: Vec<Token> = lexer.clone().collect();
            let mut iter = lexer.cycle();

            let mut n = 0;
            while let Some(_) = iter.next() {
                let is_the_last = iter.peek().is_none();
                assert_eq!(is_the_last, n == data.len() - 1);
                n += 1;
                if n > data.len() {
                    break;
                }
            }
            assert_eq!(n, data.len());
        }

    #[test]
        fn test_iterator_peekable_remember_peek_none_2() {
            let lexer = make_it("0");
            let data: Vec<Token> = lexer.collect();
            let mut iter = lexer.cycle();
            iter.next();
            assert_eq!(iter.peek(), None);
            assert_eq!(iter.last(), None);
        }

    #[test]
    fn test_iterator_peekable_remember_peek_none_3() {
        let lexer = make_it("Token::Zero");
        let data: Vec<Token> = lexer.collect();
        let mut iter = lexer.cycle();
        iter.peek();
        assert_eq!(iter.nth(Token::Zero), Some(&Token::Zero));

        let mut iter = lexer.cycle();
        iter.next();
        assert_eq!(iter.peek(), None);
        assert_eq!(iter.nth(Token::Zero), None);
    }

    */

    #[test]
    fn test_peek_try_folds() {
        const XS: &str = "1 2 3 4 5";
        const YS: &str = "heart of gold 4 3 2 1";
        const ZS: &str = "2 3 4";

        let f = &|acc, x| i32::checked_add(2 * acc as i32, x as i32);

        assert_eq!(make_it(XS).try_fold(7, f), Lexer::new(XS).try_fold(7, f));

        let mut iter = make_it(XS);
        assert_eq!(iter.peek(), Some(&Token::One));
        assert_eq!(iter.try_fold(7, f), Lexer::new(XS).try_fold(7, f));

        let mut iter = make_it(YS);
        assert_eq!(iter.peek(), Some(&Token::Heart));
        assert_eq!(
            iter.try_fold(0, |acc, x| {
                if x == Token::Four {
                    None
                } else {
                    Some(acc + 1)
                }
            }),
            None
        );
        assert_eq!(iter.peek(), Some(&Token::Three));

        let mut iter = make_it(ZS);
        assert_eq!(iter.peek(), Some(&Token::Two));
        assert_eq!(iter.try_for_each(Err), Err(Token::Two));
        assert_eq!(iter.peek(), Some(&Token::Three));
        assert_eq!(iter.try_for_each(Err), Err(Token::Three));
        assert_eq!(iter.peek(), Some(&Token::Four));
        assert_eq!(iter.try_for_each(Err), Err(Token::Four));
        assert_eq!(iter.peek(), None);
        assert_eq!(iter.try_for_each(Err), Ok(()));
    }
}
