#![deny(unused_imports)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

//! # lru-st
//!
//! This crate provides a Vec based doubly linked list implementation.
//! It also aims at providing data structures built on top of
//! doubly linked list such as LRU HashMap.
//!
//! # Features
//! - `sync`: to enable when `collections` structures needs to be used in threads
//!
//! # Example: DoublyLinkedList
//!
//! ```
//! use lru_st::DoublyLinkedList;
//!
//! let mut dll = DoublyLinkedList::new();
//! for i in 1..=3 {
//!     dll.push_back(i);
//! }
//! let c4 = dll.push_back(4);
//! assert_eq!(dll.len(), 4);
//!
//! // a Cursor is a reference to the item, not
//! // related to its position in the list.
//! let c0 = dll.push_front(0);
//!
//! // first element is 0
//! assert_eq!(dll.front(), Some(&0));
//! assert_eq!(dll.get(c0), Some(&0));
//!
//! // we move item with value 4 at front of
//! // the list
//! dll.move_front(c4).unwrap();
//! assert_eq!(dll.get_nth(0), Some(&4));
//! assert_eq!(dll.get_nth(1), Some(&0));
//! // even if order of list items changed cursors
//! // are never affected by those changes
//! assert_eq!(dll.get(c0), Some(&0));
//! ```
//!
//! # Example: LRU HashMap
//!
//! ```
//! use lru_st::collections::LruHashMap;
//!
//! let mut lru_map = LruHashMap::with_max_entries(10);
//! lru_map.insert(42, "test");
//!
//! assert_eq!(lru_map.get(&42), Some("test").as_ref());
//! assert_eq!(lru_map.len(), 1);
//!
//! // we fill the map entirely
//! for i in 0..lru_map.cap(){
//!     lru_map.insert(i, "fill");
//! }
//!
//! assert_eq!(lru_map.len(), 10);
//!
//! // this element disapeared from the map as we filled
//! // all the map without fetching it
//! assert_eq!(lru_map.get(&42), None);
//! ```
//!
//! # Example: LRU HashSet
//!
//! ```
//! use lru_st::collections::LruHashSet;
//!
//! let mut lru_set = LruHashSet::with_max_entries(10);
//!
//! assert_eq!(lru_set.insert("test"), true);
//! assert_eq!(lru_set.insert("test"), false);
//!
//! assert_eq!(lru_set.contains(&"test"), true);
//!
//! // we remove one element
//! assert_eq!(lru_set.remove(&"test"), true);
//! assert_eq!(lru_set.remove(&"test"), false);
//!
//! assert!(lru_set.is_empty());
//!
//! let mut lru_set = LruHashSet::with_max_entries(10);
//!
//! assert_eq!(lru_set.insert(String::from("will_be_erased")), true);
//!
//! for i in 0..10{
//!     assert_eq!(lru_set.insert(format!("erase_{i}")), true);
//! }
//!
//! // the item vanished as the LRU got full
//! assert_eq!(lru_set.contains(&String::from("will_be_erased")), false);
//! assert!(lru_set.is_full());
//! ```

use std::{
    fmt::{Debug, Display},
    hash::Hash,
};
use thiserror::Error;

/// Module exposing structures implemented
/// on top of [`DoublyLinkedList`]
pub mod collections;

/// Structure representing a **reference** of an element
/// within a [DoublyLinkedList]. It is important to
/// remember that a [Cursor] does not represent the
/// position of an element.
///
/// # Stale cursors
///
/// Once its element is removed, a [Cursor] becomes stale and
/// must not be used anymore. Until the freed slot is reused,
/// [DoublyLinkedList::get] and [DoublyLinkedList::pop] return
/// `None` and [DoublyLinkedList::move_front] returns
/// [Error::Uaf]. However, the next push may reuse the slot, in
/// which case the stale [Cursor] silently refers to the new
/// element. A [Cursor] is also not bound to the list that
/// created it, so using it with another list is a logic error.
///
/// ```
/// use lru_st::DoublyLinkedList;
///
/// let mut dll = DoublyLinkedList::new();
/// let c = dll.push_back(1);
/// dll.pop(c);
/// assert_eq!(dll.get(c), None);
///
/// // the freed slot is reused: `c` now refers to 2
/// dll.push_back(2);
/// assert_eq!(dll.get(c), Some(&2));
/// ```
#[derive(Debug, Clone, Hash, Copy, Eq, PartialEq)]
pub struct Cursor(usize);

impl Cursor {
    #[inline]
    const fn none() -> Self {
        Self(usize::MAX)
    }

    #[inline]
    const fn from_index(i: usize) -> Self {
        Self(i)
    }

    #[inline]
    const fn index(&self) -> usize {
        self.0
    }

    #[inline]
    const fn is_none(&self) -> bool {
        self.0 == usize::MAX
    }

    #[inline]
    const fn is_some(&self) -> bool {
        !self.is_none()
    }
}

/// A node of the doubly linked list
#[derive(Clone)]
struct Node<T> {
    prev: Cursor,
    next: Cursor,
    value: Option<T>,
}

impl<T> Node<T> {
    #[inline]
    fn free(&mut self) {
        self.prev = Cursor::none();
        self.next = Cursor::none();
        self.value = None;
    }

    #[inline]
    fn is_free(&self) -> bool {
        self.value.is_none()
    }
}

impl<T> Debug for Node<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "prev={:?} next={:?} free={:?}",
            self.prev,
            self.next,
            self.is_free()
        )
    }
}

/// [Vec] based doubly linked list implementation
///
/// # Example
///
/// ```
/// use lru_st::DoublyLinkedList;
///
/// let mut dll = DoublyLinkedList::new();
/// dll.push_front(42);
/// dll.push_front(43);
///
/// assert_eq!(dll.back(), Some(&42));
/// assert_eq!(dll.front(), Some(&43));
///
/// dll.push_back(44);
/// assert_eq!(dll.front(), Some(&43));
/// assert_eq!(dll.back(), Some(&44));
/// ```
#[derive(Clone)]
pub struct DoublyLinkedList<T> {
    // the head of the list
    head: Cursor,
    // the tail of the list
    tail: Cursor,
    // list of nodes
    list: Vec<Node<T>>,
    // free list to use for new node insertion
    free: Vec<Cursor>,
}

impl<T> Default for DoublyLinkedList<T> {
    fn default() -> Self {
        DoublyLinkedList {
            head: Cursor::none(),
            tail: Cursor::none(),
            list: Vec::new(),
            free: Vec::new(),
        }
    }
}

impl<T> Debug for DoublyLinkedList<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for v in self.iter() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", v)?;
            first = false;
        }
        write!(f, "]")
    }
}

impl<T> Display for DoublyLinkedList<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for v in self.iter() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}", v)?;
            first = false;
        }
        write!(f, "]")
    }
}

/// Enum of the possible [enum@Error] encountered while using
/// a [DoublyLinkedList]
#[derive(Debug, Error, PartialEq, PartialOrd, Ord, Eq)]
pub enum Error {
    /// Error returned when trying to access
    /// an out of bound index
    #[error("out of bound index: {0}")]
    OutOfBound(usize),

    /// Error raised when trying to use a
    /// node already freed.
    #[error("stale cursor: its element has already been removed from the list")]
    Uaf,
}

impl<T> PartialEq for DoublyLinkedList<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        let mut other_it = other.iter();

        for v in self.iter() {
            match other_it.next() {
                Some(ov) => {
                    if v != ov {
                        return false;
                    }
                }
                None => return false,
            }
        }

        true
    }
}

impl<T> FromIterator<T> for DoublyLinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut d = Self::new();
        for e in iter {
            d.push_back(e);
        }
        d
    }
}

impl<T> DoublyLinkedList<T> {
    /// Creates a new empty [DoublyLinkedList]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new empty [DoublyLinkedList] with a given capacity
    pub fn with_capacity(capacity: usize) -> Self {
        DoublyLinkedList {
            list: Vec::with_capacity(capacity),
            ..Default::default()
        }
    }

    /// Creates a new [DoublyLinkedList] from a [Vec]
    #[deprecated(
        since = "0.4.0",
        note = "use `collect()` or `DoublyLinkedList::from_iter` instead"
    )]
    pub fn from_vec(v: Vec<T>) -> Self {
        Self::from_iter(v)
    }

    /// Returns true if the list is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    fn next_available_cursor(&mut self) -> Cursor {
        self.free
            .pop()
            .unwrap_or(Cursor::from_index(self.list.len()))
    }

    #[inline]
    fn put(&mut self, e: Node<T>, at: Cursor) {
        if at.index() == self.list.len() {
            self.list.push(e);
            return;
        }
        self.list[at.index()] = e;
    }

    /// Get the cursor of nth element
    #[inline]
    fn get_nth_cursor(&self, mut n: usize) -> Option<Cursor> {
        if n >= self.len() {
            return None;
        }

        let c = if n < self.len() / 2 {
            // search from head
            let mut next = self.head;
            while next.is_some() && n > 0 {
                next = self.list[next.index()].next;
                n -= 1;
            }
            next
        } else {
            // search from tail
            let mut prev = self.tail;
            n = self.len() - n - 1;
            while prev.is_some() && n > 0 {
                prev = self.list[prev.index()].prev;
                n -= 1;
            }
            prev
        };

        if n == 0 {
            return Some(c);
        }

        None
    }

    /// Pushes an element to the front of the list
    #[inline]
    pub fn push_front(&mut self, v: T) -> Cursor {
        let cursor = self.next_available_cursor();
        let node = Node {
            prev: Cursor::none(),
            next: self.head,
            value: Some(v),
        };

        // if there is no tail
        if self.tail.is_none() {
            self.tail = cursor;
        }

        // we link the old head (if existing) to the new one
        self.new_prev(self.head, cursor);

        // we insert element at position
        self.put(node, cursor);
        // new head
        self.head = cursor;
        cursor
    }

    /// Pushes an element to the back of the list and returning
    /// the [Cursor] pointing to this element. The [Cursor] can
    /// then be used to directly access/move/pop element.
    #[inline]
    pub fn push_back(&mut self, v: T) -> Cursor {
        let cursor = self.next_available_cursor();
        // element to be inserted at the end
        let e = Node {
            prev: self.tail,
            next: Cursor::none(),
            value: Some(v),
        };

        // if there is no head we set it
        if self.head.is_none() {
            self.head = cursor;
        }

        // we link the old tail (if existing) to the new one
        self.new_next(self.tail, cursor);

        // we insert element at position
        self.put(e, cursor);
        // new tail
        self.tail = cursor;
        cursor
    }

    /// Get the element in the list at a given [Cursor] or None
    /// if there is no element. If wanting to get an element at
    /// a given position see [DoublyLinkedList::get_nth].
    #[inline]
    pub fn get(&self, c: Cursor) -> Option<&T> {
        self.list.get(c.index()).and_then(|n| n.value.as_ref())
    }

    /// Get an element given its position in the list
    #[inline]
    pub fn get_nth(&self, n: usize) -> Option<&T> {
        self.get(self.get_nth_cursor(n)?)
    }

    /// Get a mutable element at a given position in the list or None
    /// if there is no element.
    #[inline]
    pub fn get_mut(&mut self, c: Cursor) -> Option<&mut T> {
        self.list.get_mut(c.index()).and_then(|n| n.value.as_mut())
    }

    /// Get an element given its position in the list
    #[inline]
    pub fn get_mut_nth(&mut self, n: usize) -> Option<&mut T> {
        self.get_mut(self.get_nth_cursor(n)?)
    }

    /// Get the element at the front of the list
    #[inline]
    pub fn front(&self) -> Option<&T> {
        self.get(self.head)
    }

    /// Get a mutable reference to the element at the front of the list
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.get_mut(self.head)
    }

    /// Get the element a the back of the list
    #[inline]
    pub fn back(&self) -> Option<&T> {
        self.get(self.tail)
    }

    /// Get a mutable reference to the element at the back of the list
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.get_mut(self.tail)
    }

    /// Returns the number of elements in the list
    #[inline]
    pub fn len(&self) -> usize {
        self.list.len() - self.free.len()
    }

    /// Pops the element a the back of the list
    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        if self.tail.is_some() {
            self._pop(self.tail)
        } else {
            None
        }
    }

    #[inline]
    fn new_prev(&mut self, at: Cursor, prev: Cursor) {
        // if there is something at pos
        if at.is_some() {
            // we modify element at pos
            self.list[at.index()].prev = prev
        }
    }

    #[inline]
    fn new_next(&mut self, at: Cursor, next: Cursor) {
        if at.is_some() {
            // we modify element at pos
            self.list[at.index()].next = next;
        }
    }

    /// Provides an iterator (i.e. [DoublyLinkedListIter]) over the elements of the list
    #[inline]
    pub fn iter<'a>(&'a self) -> DoublyLinkedListIter<'a, T> {
        DoublyLinkedListIter {
            dll: self,
            front_cursor: self.head,
            back_cursor: self.tail,
            len: self.len(),
        }
    }

    #[inline]
    pub(crate) fn move_front_unchecked(&mut self, at: Cursor) {
        let i = at.index();
        let node = &mut self.list[i];
        debug_assert!(!node.is_free());

        // if we are not processing head
        if node.prev.is_some() {
            let (next, prev) = (node.next, node.prev);
            // we link next to prev
            self.new_prev(next, prev);
            // we link prev to next
            self.new_next(prev, next);

            // we are processing the tail so we have to assign a new one
            if next.is_none() {
                self.tail = prev
            }

            // linking old head to the new head
            self.new_prev(self.head, at);

            // we make item the new head
            let node = &mut self.list[i];
            node.next = self.head;
            node.prev = Cursor::none();
            self.head = at;
        }
    }

    /// Move item at cursor to the head of list
    #[inline]
    pub fn move_front(&mut self, at: Cursor) -> Result<(), Error> {
        let node = self
            .list
            .get(at.index())
            .ok_or(Error::OutOfBound(at.index()))?;

        // only detects stale cursors until their slot is reused
        if node.is_free() {
            return Err(Error::Uaf);
        }

        self.move_front_unchecked(at);
        Ok(())
    }

    /// Pops the item at front of the doubly linked list
    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        if self.head.is_some() {
            self._pop(self.head)
        } else {
            None
        }
    }

    /// Pops the item located at `at` [Cursor] in the doubly linked list.
    /// This API pops an element according to its [Cursor] which is
    /// not corresponding to its position within the linked list.
    /// To pop an item according to its position in the linked list
    /// use `pop_nth`.
    #[inline]
    pub fn pop(&mut self, at: Cursor) -> Option<T> {
        match self.list.get(at.index()) {
            Some(n) if !n.is_free() => self._pop(at),
            _ => None,
        }
    }

    /// Pops the nth element of linked list
    #[inline]
    pub fn pop_nth(&mut self, n: usize) -> Option<T> {
        self.pop(self.get_nth_cursor(n)?)
    }

    #[inline]
    fn _pop(&mut self, at: Cursor) -> Option<T> {
        debug_assert!(!self.list[at.index()].is_free());

        let node = &mut self.list[at.index()];

        // if we want to remove head
        if at == self.head {
            let new_head = node.next;
            self.head = new_head;
        }

        // if we want to remove tail
        if at == self.tail {
            let new_tail = node.prev;
            self.tail = new_tail;
        }

        let (next, prev) = (node.next, node.prev);
        // actually unlinking the at Cursor
        self.new_prev(next, prev);
        self.new_next(prev, next);

        let node = &mut self.list[at.index()];
        let out = node.value.take();
        // mark node at Cursor as free
        node.free();
        self.free.push(at);

        out
    }

    #[inline]
    #[cfg(test)]
    fn verify(&self) {
        let mut prev = Cursor::none();
        let mut oc = self.head;
        while oc.is_some() {
            let node = self.list.get(oc.index()).unwrap();
            // we check back link
            assert_eq!(node.prev, prev);
            prev = oc;
            oc = node.next;
        }
    }
}

/// [DoublyLinkedList] iterator
pub struct DoublyLinkedListIter<'a, T> {
    dll: &'a DoublyLinkedList<T>,
    front_cursor: Cursor,
    back_cursor: Cursor,
    len: usize,
}

impl<'a, T> Iterator for DoublyLinkedListIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        let node = self.dll.list.get(self.front_cursor.index())?;
        self.front_cursor = node.next;
        self.len -= 1;
        node.value.as_ref()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<T> ExactSizeIterator for DoublyLinkedListIter<'_, T> {}

impl<T> std::iter::FusedIterator for DoublyLinkedListIter<'_, T> {}

impl<'a, T> DoubleEndedIterator for DoublyLinkedListIter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        // nodes pointed by others should always be valid
        let node = self.dll.list.get(self.back_cursor.index())?;
        self.back_cursor = node.prev;
        self.len -= 1;
        node.value.as_ref()
    }
}

/// Macro used to create a [DoublyLinkedList]
///
/// # Example
///
/// ```
/// use lru_st::dll;
///
/// let d = dll![1,2,3];
/// assert_eq!(d, dll![1,2,3]);
/// assert_ne!(d, dll![3,2,1]);
/// ```
#[macro_export]
macro_rules! dll {
    [$($item:literal),*] => {
        {
            let mut dll=$crate::DoublyLinkedList::new();
            $(dll.push_back($item);)*
            dll
        }
    };
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;

    use super::*;

    #[test]
    #[allow(deprecated)]
    fn dll_from_vec_test() {
        let len = 100;
        let d = DoublyLinkedList::from_vec((0..len).collect());
        println!("{}", d);
        let mut i = 0;

        // from_vec must insert values in the same order they appear in the vector
        #[allow(clippy::explicit_counter_loop)]
        for v in d.iter() {
            assert_eq!(v, &i);
            i += 1;
        }
    }

    #[test]
    fn dll_rev_iter_test() {
        let d: DoublyLinkedList<_> = (1..=5).collect();
        println!("{}", d);
        let mut iter = d.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next_back(), Some(&5));
        assert_eq!(iter.next_back(), Some(&4));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn dll_iter_test() {
        let len = 100;
        let d: DoublyLinkedList<_> = (0..len).collect();

        let mut i = len - 1;
        for v in d.iter().rev() {
            assert_eq!(v, &i);
            i -= 1;
        }

        assert_eq!(i, -1);
    }

    #[test]
    fn dll_push_back_test() {
        let len = 100;
        let mut d = DoublyLinkedList::new();

        for i in 0..len {
            d.push_back(i);
        }

        assert_eq!(d.len(), len);

        for i in (0..len).rev() {
            let back = d.pop_back();
            assert!(back.is_some(), "iteration {i}");
            assert_eq!(back.unwrap(), i, "iteration {i}");
            assert!(d.list[i].is_free());
            assert!(d.free.iter().all(|c| d.list[c.index()].is_free()));
        }

        assert!(d.is_empty());
        assert!(d.head.is_none());
        assert!(d.tail.is_none());
        assert_eq!(d.free.len(), len);
        assert!(d.list.iter().all(Node::is_free));
    }

    #[test]
    fn dll_push_front_test() {
        let len = 100;

        let mut d = DoublyLinkedList::new();

        for i in (0..len).rev() {
            d.push_front(i);
        }

        assert_eq!(d.len(), len);

        for i in (0..len).rev() {
            assert_eq!(d.pop_back().unwrap(), i);
            assert!(d.list[len - i - 1].is_free());
            assert!(d.free.iter().all(|c| d.list[c.index()].is_free()));
        }

        assert!(d.is_empty());
        assert!(d.head.is_none());
        assert!(d.tail.is_none());
        assert_eq!(d.free.len(), len);
        assert!(d.list.iter().all(Node::is_free));
    }

    #[test]
    fn dll_move_front_test() {
        let len = 100;

        let mut d = DoublyLinkedList::new();

        for i in 0..len {
            d.push_front(i);
        }

        for i in (0..len).rev() {
            println!("moving {} to front", d.get(Cursor::from_index(i)).unwrap());
            d.move_front(Cursor::from_index(i)).unwrap();
            assert_eq!(d.front().unwrap(), &i);
        }
    }

    #[test]
    fn dll_pop_front_test() {
        let len = 100;

        let mut d = DoublyLinkedList::new();

        for i in 0..len {
            d.push_front(i);
        }

        for i in (0..len).rev() {
            d.verify();
            assert_eq!(d.pop_front(), Some(i));
        }

        assert_eq!(d.len(), 0);
    }

    #[test]
    fn dll_pop_test_simple() {
        let mut dll = dll![1, 2, 3, 4, 5];
        assert_eq!(dll.pop(Cursor::from_index(2)), Some(3));
        assert_eq!(dll.pop(Cursor::from_index(3)), Some(4));
        // two values got popped in the middle so pop_front
        // should not return them
        assert_eq!(dll.pop_front(), Some(1));
        assert_eq!(dll.pop_front(), Some(2));
        assert_eq!(dll.pop_back(), Some(5));
        assert!(dll.is_empty());
    }

    #[test]
    fn dll_pop_nth() {
        let mut dll = dll![1, 2, 3, 4, 5];
        dll.move_front(Cursor::from_index(2)).unwrap();
        assert_eq!(dll.pop_nth(2), Some(2));
    }

    #[test]
    fn dll_iter_mixed_ends() {
        let one = dll![1];
        let mut it = one.iter();
        assert_eq!(it.next_back(), Some(&1));
        assert_eq!(it.next(), None);
        assert_eq!(it.next_back(), None);

        let two = dll![1, 2];
        let mut it = two.iter();
        assert_eq!(it.next(), Some(&1));
        assert_eq!(it.next_back(), Some(&2));
        assert_eq!(it.next(), None);
        assert_eq!(it.next_back(), None);

        let mut it = two.iter();
        assert_eq!(it.next_back(), Some(&2));
        assert_eq!(it.next(), Some(&1));
        assert_eq!(it.next_back(), None);

        let empty: DoublyLinkedList<i32> = DoublyLinkedList::new();
        assert_eq!(empty.iter().next(), None);
        assert_eq!(empty.iter().next_back(), None);
    }

    #[test]
    fn dll_iter_size_hint() {
        let dll = dll![1, 2, 3];
        let mut it = dll.iter();
        assert_eq!(it.len(), 3);
        it.next();
        it.next_back();
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next(), Some(&2));
        assert_eq!(it.len(), 0);
        assert_eq!(it.next(), None);
        assert_eq!(it.next_back(), None);
    }

    #[test]
    fn dll_move_front_freed() {
        let mut dll = DoublyLinkedList::new();
        let c = dll.push_back(1);
        dll.push_back(2);

        assert_eq!(dll.pop(c), Some(1));
        assert!(matches!(dll.move_front(c), Err(Error::Uaf)));
        assert_eq!(dll.front(), Some(&2));

        assert!(matches!(
            dll.move_front(Cursor::from_index(42)),
            Err(Error::OutOfBound(42))
        ));
    }

    #[test]
    fn dll_pop_invalid_cursor() {
        let mut dll = DoublyLinkedList::new();
        let c = dll.push_back(1);
        dll.push_back(2);

        assert_eq!(dll.pop(c), Some(1));
        assert_eq!(dll.pop(c), None);
        assert_eq!(dll.pop(Cursor::from_index(42)), None);
        assert_eq!(dll.pop(Cursor::none()), None);
        assert_eq!(dll.len(), 1);
        dll.verify();
    }

    #[test]
    fn dll_move_front_head_tail() {
        let mut dll = DoublyLinkedList::new();
        let c1 = dll.push_back(1);
        dll.push_back(2);
        let c3 = dll.push_back(3);

        // moving the head is a no-op
        dll.move_front(c1).unwrap();
        assert_eq!(dll.iter().copied().collect::<Vec<_>>(), [1, 2, 3]);

        // moving the tail updates the tail
        dll.move_front(c3).unwrap();
        assert_eq!(dll.iter().copied().collect::<Vec<_>>(), [3, 1, 2]);
        assert_eq!(dll.back(), Some(&2));
        dll.verify();

        // single element list
        let mut one = DoublyLinkedList::new();
        let c = one.push_back(1);
        one.move_front(c).unwrap();
        assert_eq!(one.front(), Some(&1));
        assert_eq!(one.back(), Some(&1));
    }

    #[test]
    fn dll_pop_head_tail() {
        let mut dll = DoublyLinkedList::new();
        let c1 = dll.push_back(1);
        dll.push_back(2);
        let c3 = dll.push_back(3);

        assert_eq!(dll.pop(c1), Some(1));
        assert_eq!(dll.front(), Some(&2));
        assert_eq!(dll.pop(c3), Some(3));
        assert_eq!(dll.back(), Some(&2));
        assert_eq!(dll.front(), Some(&2));
        dll.verify();

        assert_eq!(dll.pop_front(), Some(2));
        assert!(dll.is_empty());
        assert!(dll.head.is_none());
        assert!(dll.tail.is_none());
    }

    #[test]
    fn dll_pop_test() {
        let mut rng = thread_rng();
        let len = 100;

        let mut d = DoublyLinkedList::new();

        for i in 0..len {
            d.push_front(i);
        }

        let mut cursors: Vec<usize> = (0..len).collect();
        cursors.shuffle(&mut rng);

        for (i, c) in cursors.iter().map(|i| (*i, Cursor::from_index(*i))) {
            d.verify();
            assert_eq!(d.get(c), Some(&i));
            assert_eq!(d.pop(c), Some(i));
            assert_eq!(d.pop(c), None);
        }

        assert_eq!(d.len(), 0);
    }

    #[test]
    fn dll_eq_test() {
        assert_eq!(dll![1, 2, 3], dll![1, 2, 3]);
        assert_ne!(dll![1, 2, 3], dll![1, 2]);
    }

    #[test]
    fn get_nth_test() {
        let dll: DoublyLinkedList<_> = [10, 20, 30, 40].into_iter().collect();

        assert_eq!(dll.get(Cursor::from_index(2)), Some(&30));
        assert_eq!(dll.get_nth(0), Some(&10));
        assert_eq!(dll.get_nth(1), Some(&20));
        assert_eq!(dll.get_nth(2), Some(&30));
        assert_eq!(dll.get_nth(3), Some(&40));
        assert_eq!(dll.get_nth(4), None); // Out of bounds
        assert_eq!(dll.get_nth(100), None); // Far out of bounds
    }

    #[test]
    fn get_nth_empty_test() {
        let dll: DoublyLinkedList<i32> = DoublyLinkedList::new();
        assert_eq!(dll.get_nth(0), None);
    }
}
