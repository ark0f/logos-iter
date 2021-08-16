#![doc = include_str!("../README.md")]
#![cfg_attr(not(test), no_std)]

mod peekable;

pub use peekable::PeekableLexer;

use logos::{Lexer, Logos, Source, Span};

pub trait LogosIter<'source, T>: Iterator<Item = T>
where
    T: Logos<'source>,
{
    fn span(&self) -> Span;

    fn slice(&self) -> &'source <T::Source as Source>::Slice;

    fn source(&self) -> &'source T::Source;

    fn remainder(&self) -> &'source <T::Source as Source>::Slice;

    fn bump(&mut self, n: usize);

    fn extras(&self) -> &T::Extras;

    fn extras_mut(&mut self) -> &mut T::Extras;

    /// See [`PeekableLexer`].
    fn peekable_lexer(self) -> PeekableLexer<'source, Self, T>
    where
        Self: Sized,
    {
        PeekableLexer {
            lexer: self,
            peeked: None,
        }
    }
}

impl<'source, T> LogosIter<'source, T> for Lexer<'source, T>
where
    T: Logos<'source>,
{
    fn span(&self) -> Span {
        Lexer::span(self)
    }

    fn slice(&self) -> &'source <T::Source as Source>::Slice {
        Lexer::slice(self)
    }

    fn source(&self) -> &'source T::Source {
        Lexer::source(self)
    }

    fn remainder(&self) -> &'source <T::Source as Source>::Slice {
        Lexer::remainder(self)
    }

    fn bump(&mut self, n: usize) {
        Lexer::bump(self, n)
    }

    fn extras(&self) -> &T::Extras {
        &self.extras
    }

    fn extras_mut(&mut self) -> &mut T::Extras {
        &mut self.extras
    }
}
