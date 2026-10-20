use std::{collections::HashMap, hash::Hash};

#[cfg(not(feature = "sync"))]
use std::rc::{Rc, Weak};

#[cfg(feature = "sync")]
use {std::sync::Arc as Rc, std::sync::Weak};

use crate::{Cursor, DoublyLinkedList, DoublyLinkedListIter};

/// An iterator over the items of a [LruHashSet].
pub struct Iter<'a, K>
where
    K: Hash + Eq,
{
    lru_iter: DoublyLinkedListIter<'a, Weak<K>>,
}

impl<'a, K> Iterator for Iter<'a, K>
where
    K: Hash + Eq,
{
    type Item = Rc<K>;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.lru_iter.next() {
            return item.upgrade();
        }
        None
    }
}

impl<'a, K> DoubleEndedIterator for Iter<'a, K>
where
    K: Hash + Eq,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(item) = self.lru_iter.next_back() {
            return item.upgrade();
        }
        None
    }
}

/// A LRU HashSet implementation
pub struct LruHashSet<K> {
    map: HashMap<Rc<K>, Cursor>,
    lru: DoublyLinkedList<Weak<K>>,
    max_entries: usize,
}

impl<K> LruHashSet<K>
where
    K: Hash + Eq,
{
    /// Creates a new [LruHashSet] with a given number of entries
    pub fn with_max_entries(max_entries: usize) -> Self {
        LruHashSet {
            map: HashMap::with_capacity(max_entries),
            lru: DoublyLinkedList::with_capacity(max_entries),
            max_entries,
        }
    }

    /// Returns a reference to the value in the set, if any, that is equal to the given value.
    #[inline]
    pub fn get(&mut self, k: &K) -> Option<Rc<K>> {
        if let Some(k) = self.map.get(k).and_then(|cursor| {
            self.lru.move_front_unchecked(*cursor);
            self.lru.front()
        }) {
            return k.upgrade();
        }
        None
    }

    /// Returns an iterator over the values within the set
    ///
    /// # Warning
    ///
    /// Iterating does not modify the order of the LRU to prevent
    /// any unwanted side effects due.
    pub fn iter<'a>(&'a mut self) -> Iter<'a, K> {
        Iter {
            lru_iter: self.lru.iter(),
        }
    }

    /// Returns `true` if there is an element is in the set
    #[inline]
    pub fn contains(&mut self, k: &K) -> bool {
        self.get(k).is_some()
    }

    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    ///
    /// - If the set did not previously contain this value, `true` is returned.
    /// - If the set already contained this value, `false` is returned,
    ///   and the set is not modified: original value is not replaced,
    ///   and the value passed as argument is dropped.
    #[inline]
    pub fn insert(&mut self, k: K) -> bool {
        // we update value if already there
        if self.contains(&k) {
            return false;
        }

        // if we arrive here the key/value needs to be inserted
        // if we reached capacity, we must delete the last used entry first
        if self.map.len() == self.max_entries {
            if let Some(k) = self.lru.pop_back() {
                // we put this in a block so that we can debug_assert latter
                {
                    let key = k.upgrade().expect("weak reference must be valid");
                    self.map.remove(&key);
                }
                // Rc should have been dropped now because we have removed item from map
                debug_assert!(k.upgrade().is_none());
            };
        }
        let k = Rc::new(k);
        let cursor = self.lru.push_front(Rc::downgrade(&k));
        self.map.insert(k, cursor);
        true
    }

    /// Removes an entry from the `LruHashSet` and returns `true`
    /// if the entry was removed else `false`
    #[inline]
    pub fn remove(&mut self, k: &K) -> bool {
        if let Some(c) = self.map.remove(k) {
            if self.lru.pop(c).is_some() {
                return true;
            }
        }
        false
    }

    /// Returns the length of the `LruHashSet`
    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns the capacity of the `LruHashSet`
    #[inline]
    pub fn cap(&self) -> usize {
        self.max_entries
    }

    /// Returns `true` if the `LruHashSet` is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns `true` if the `LruHashSet` is full
    #[inline]
    pub fn is_full(&self) -> bool {
        self.max_entries == self.map.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_hashset_test() {
        let max_entries = 1000;
        let mut lru = LruHashSet::with_max_entries(max_entries);
        assert!(lru.is_empty());

        for i in 0..max_entries * 2 {
            assert!(lru.insert(i));
            assert!(lru.contains(&i));
        }

        // all values until max_entries must have been
        // rotated in the LRU so not contained anymore
        for i in 0..max_entries {
            assert!(!lru.contains(&i));
        }

        // all values above max_entries must be contained
        for i in max_entries + 1..max_entries * 2 {
            assert!(lru.contains(&i));
        }
    }

    #[test]
    fn hashset_get_test() {
        let mut lru = LruHashSet::with_max_entries(10);

        lru.insert(42);
        assert_eq!(lru.get(&42), Some(Rc::new(42)));
    }

    #[test]
    #[allow(clippy::bool_assert_comparison)]
    fn hashset_remove_test() {
        let mut lru = LruHashSet::with_max_entries(10);

        assert_eq!(lru.insert(42), true);
        assert_eq!(lru.insert(42), false);
        assert_eq!(lru.remove(&42), true);
        assert_eq!(lru.remove(&42), false);
    }

    #[test]
    fn hashset_iter() {
        let mut lru = LruHashSet::with_max_entries(10);

        lru.insert(41);
        lru.insert(42);
        lru.insert(43);
        let mut iter = lru.iter();
        assert_eq!(iter.next(), Some(Rc::new(43)));
        assert_eq!(iter.next(), Some(Rc::new(42)));
        assert_eq!(iter.next(), Some(Rc::new(41)));
        assert_eq!(iter.next(), None);

        // we remove one item
        lru.remove(&42);
        let mut iter = lru.iter().rev();
        assert_eq!(iter.next(), Some(Rc::new(41)));
        assert_eq!(iter.next(), Some(Rc::new(43)));
        assert_eq!(iter.next(), None);
    }
}
