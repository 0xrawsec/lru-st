use crate::{Cursor, DoublyLinkedList, DoublyLinkedListIter};

use std::{collections::HashMap, fmt::Display, hash::Hash};

#[cfg(not(feature = "sync"))]
use std::rc::{Rc, Weak};

#[cfg(feature = "sync")]
use {std::sync::Arc as Rc, std::sync::Weak};

/// An iterator over the entries of an `LruHashMap`, in order from most recently used to least recently used.
///
/// This iterator yields references to the key-value pairs stored in the `LruHashMap`.
/// The keys are returned as `Rc<K>`, and the values as `&V`.
///
/// # Type Parameters
/// - `'a`: The lifetime of the `LruHashMap` being iterated over.
/// - `K`: The type of keys in the `LruHashMap`.
/// - `V`: The type of values in the `LruHashMap`.
pub struct LruHashmapIter<'a, K, V> {
    it: DoublyLinkedListIter<'a, (Weak<K>, V)>,
}

impl<'a, K, V> LruHashmapIter<'a, K, V> {
    fn from_lru_hashmap(map: &'a LruHashMap<K, V>) -> LruHashmapIter<'a, K, V> {
        Self { it: map.lru.iter() }
    }
}

impl<'a, K, V> Iterator for LruHashmapIter<'a, K, V> {
    type Item = (Rc<K>, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        let item = self.it.next()?;
        // Safe to unwrap because the key is guaranteed to exist in the map
        let k = item
            .0
            .upgrade()
            .expect("weak reference must be valid because the key exists in the map");
        Some((k, &(item.1)))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.it.size_hint()
    }
}

impl<K, V> ExactSizeIterator for LruHashmapIter<'_, K, V> {}

impl<K, V> std::iter::FusedIterator for LruHashmapIter<'_, K, V> {}

impl<'a, K, V> DoubleEndedIterator for LruHashmapIter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let item = self.it.next_back()?;
        // Safe to unwrap because the key is guaranteed to exist in the map
        let k = item
            .0
            .upgrade()
            .expect("weak reference must be valid because the key exists in the map");
        Some((k, &(item.1)))
    }
}

/// A Least Recently Used (LRU) cache implemented on top of [`HashMap`] and [`DoublyLinkedList`] list.
///
/// The `LruHashMap` maintains a maximum number of entries. When the cache is full and a new
/// entry is inserted, the least recently used entry is removed.
///
/// # Type Parameters
/// - `K`: The type of keys in the cache. Must implement `Hash` and `Eq`.
/// - `V`: The type of values in the cache.
///
/// # Examples
/// ```
/// use lru_st::collections::LruHashMap;
///
/// let mut cache = LruHashMap::with_max_entries(2);
/// cache.insert("a", 1);
/// cache.insert("b", 2);
/// assert_eq!(cache.get(&"a"), Some(&1));
/// cache.insert("c", 3);
/// assert_eq!(cache.get(&"a"), Some(&1));
/// assert_eq!(cache.get(&"b"), None); // "b" was evicted
/// ```
pub struct LruHashMap<K, V> {
    map: HashMap<Rc<K>, Cursor>,
    lru: DoublyLinkedList<(Weak<K>, V)>,
    max_entries: usize,
}

impl<K, V> LruHashMap<K, V>
where
    K: Hash + Eq,
{
    /// Creates a new, empty `LruHashMap` with the specified maximum number of entries.
    ///
    /// # Arguments
    /// * `max_entries` - The maximum number of entries the cache can hold.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// cache.insert("a", 1);
    /// cache.insert("b", 2);
    /// assert_eq!(cache.get(&"a"), Some(&1));
    /// cache.insert("c", 3);
    /// assert_eq!(cache.get(&"a"), Some(&1));
    /// assert_eq!(cache.get(&"b"), None); // "b" was evicted
    /// ```
    pub fn with_max_entries(max_entries: usize) -> Self {
        LruHashMap {
            map: HashMap::with_capacity(max_entries),
            lru: DoublyLinkedList::with_capacity(max_entries),
            max_entries,
        }
    }

    /// Returns a reference to the value associated with the given key,
    /// if it exists. The key is moved to the front of the LRU list.
    ///
    /// # Arguments
    /// * `k` - The key to look up.
    ///
    /// # Returns
    /// `Some(&V)` if the key exists, `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// cache.insert("a", 1);
    /// assert_eq!(cache.get(&"a"), Some(&1));
    /// ```
    #[inline]
    pub fn get(&mut self, k: &K) -> Option<&V> {
        if let Some((_k, v)) = self.map.get(k).and_then(|cursor| {
            self.lru.move_front_unchecked(*cursor);
            self.lru.front()
        }) {
            return Some(v);
        }
        None
    }

    /// Returns a mutable reference to the value associated with the given key,
    /// if it exists. The key is moved to the front of the LRU list.
    ///
    /// # Arguments
    /// * `k` - The key to look up.
    ///
    /// # Returns
    /// `Some(&mut V)` if the key exists, `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// cache.insert("a", 1);
    /// if let Some(v) = cache.get_mut(&"a") {
    ///     *v = 2;
    /// }
    /// assert_eq!(cache.get(&"a"), Some(&2));
    /// ```
    #[inline]
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        if let Some((_k, v)) = self.map.get(k).and_then(|cursor| {
            self.lru.move_front_unchecked(*cursor);
            self.lru.front_mut()
        }) {
            return Some(v);
        }
        None
    }

    /// Returns an iterator over the key-value pairs in the `LruHashMap`,
    /// ordered from most recently used to least recently used.
    ///
    /// # Returns
    /// An iterator yielding `(Rc<K>, &V)` pairs.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// #[cfg(not(feature = "sync"))]
    /// use std::rc::Rc;
    ///
    /// #[cfg(feature = "sync")]
    /// use std::sync::Arc as Rc;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// cache.insert("a", 1);
    /// cache.insert("b", 2);
    ///
    /// let mut iter = cache.items();
    /// assert_eq!(iter.next(), Some((Rc::new("b"), &2)));
    /// assert_eq!(iter.next(), Some((Rc::new("a"), &1)));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    pub fn items(&self) -> LruHashmapIter<'_, K, V> {
        LruHashmapIter::from_lru_hashmap(self)
    }

    /// Returns an iterator over the keys in the `LruHashMap`,
    /// ordered from most recently used to least recently used.
    ///
    /// # Returns
    /// An iterator yielding `Rc<K>` keys.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    /// #[cfg(not(feature = "sync"))]
    /// use std::rc::Rc;
    ///
    /// #[cfg(feature = "sync")]
    /// use std::sync::Arc as Rc;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// cache.insert("a", 1);
    /// cache.insert("b", 2);
    ///
    /// let mut keys = cache.keys();
    /// assert_eq!(keys.next(), Some(Rc::new("b")));
    /// assert_eq!(keys.next(), Some(Rc::new("a")));
    /// assert_eq!(keys.next(), None);
    #[inline]
    pub fn keys(&self) -> impl DoubleEndedIterator<Item = Rc<K>> + use<'_, K, V> {
        self.items().map(|(k, _)| k)
    }

    /// Returns an iterator over the values in the `LruHashMap`,
    /// ordered from most recently used to least recently used.
    ///
    /// # Returns
    /// An iterator yielding `&V` values.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// cache.insert("a", 1);
    /// cache.insert("b", 2);
    ///
    /// let mut values = cache.values();
    /// assert_eq!(values.next(), Some(&2));
    /// assert_eq!(values.next(), Some(&1));
    /// assert_eq!(values.next(), None);
    /// ```
    #[inline]
    pub fn values(&self) -> impl DoubleEndedIterator<Item = &V> + use<'_, K, V> {
        self.items().map(|(_, v)| v)
    }

    /// Checks if the cache contains the given key.
    ///
    /// # Arguments
    /// * `k` - The key to check.
    ///
    /// # Returns
    /// `true` if the key exists, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// cache.insert("a", 1);
    /// assert!(cache.contains_key(&"a"));
    /// assert!(!cache.contains_key(&"b"));
    /// ```
    #[inline]
    pub fn contains_key(&mut self, k: &K) -> bool {
        self.get(k).is_some()
    }

    /// Inserts a key-value pair into the cache. If the cache is full,
    /// the least recently used entry is removed and returned.
    ///
    /// # Arguments
    /// * `k` - The key to insert.
    /// * `v` - The value to insert.
    ///
    /// # Returns
    /// `Some((K, V))` if an entry was evicted, `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(1);
    /// cache.insert("a", 1);
    /// let evicted = cache.insert("b", 2);
    /// assert_eq!(evicted, Some(("a", 1)));
    /// ```
    #[inline]
    pub fn insert(&mut self, k: K, v: V) -> Option<(K, V)> {
        let mut removed = None;
        // we update value if already there
        if let Some(old) = self.get_mut(&k) {
            *old = v;
            return removed;
        }
        // if we arrive here the key/value needs to be inserted
        // if we reached capacity, we must delete the last used entry first
        if self.map.len() == self.max_entries {
            removed = self.pop_lru();
        }
        let k = Rc::new(k);
        let cursor = self.lru.push_front((Rc::downgrade(&k), v));
        self.map.insert(k, cursor);
        removed
    }

    /// Removes the entry associated with the given key from the cache.
    ///
    /// # Arguments
    /// * `k` - The key to remove.
    ///
    /// # Returns
    /// `Some(V)` if the key existed, `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// cache.insert("a", 1);
    /// assert_eq!(cache.remove(&"a"), Some(1));
    /// assert_eq!(cache.remove(&"b"), None);
    /// ```
    #[inline]
    pub fn remove(&mut self, k: &K) -> Option<V> {
        if let Some(c) = self.map.remove(k) {
            if let Some((_k, v)) = self.lru.pop(c) {
                return Some(v);
            }
        }
        None
    }

    /// Removes and returns the least recently used entry from the cache.
    ///
    /// This function removes the key-value pair at the back of the LRU list (the least recently used entry)
    /// and returns it. If the cache is empty, it returns `None`.
    ///
    /// # Returns
    /// `Some((K, V))` if an entry was removed, `None` if the cache is empty.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// cache.insert("a", 1);
    /// cache.insert("b", 2);
    /// assert_eq!(cache.pop_lru(), Some(("a", 1)));
    /// assert_eq!(cache.len(), 1);
    /// assert_eq!(cache.pop_lru(), Some(("b", 2)));
    /// assert_eq!(cache.pop_lru(), None);
    /// ```
    #[inline]
    pub fn pop_lru(&mut self) -> Option<(K, V)> {
        let mut removed = None;
        if let Some((k, v)) = self.lru.pop_back() {
            // we put this in a block so that we can debug_assert latter
            {
                // Safe to unwrap because the key is guaranteed to exist in the map
                let key = k.upgrade().expect("weak reference must be valid");
                self.map.remove(&key);

                // it cannot be None as key is a strong reference
                if let Some(inner_key) = Rc::into_inner(key) {
                    removed = Some((inner_key, v));
                }
            }
            // Rc should have been dropped now because we have removed item from map
            debug_assert!(k.upgrade().is_none());
        };
        removed
    }

    /// Returns the number of entries in the cache.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// assert_eq!(cache.len(), 0);
    /// cache.insert("a", 1);
    /// assert_eq!(cache.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns the maximum number of entries the cache can hold.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// cache.insert("a", 1);
    /// assert_eq!(cache.cap(), 2);
    /// ```
    #[inline]
    pub fn cap(&self) -> usize {
        self.max_entries
    }

    /// Checks if the cache is empty.
    ///
    /// # Examples
    /// ```
    /// use lru_st::collections::LruHashMap;
    ///
    /// let mut cache = LruHashMap::with_max_entries(2);
    /// assert!(cache.is_empty());
    /// cache.insert("a", 1);
    /// assert!(!cache.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl<K, V> Display for LruHashMap<K, V>
where
    K: Display,
    V: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        write!(f, "{{")?;
        for v in self.lru.iter() {
            let key = v.0.upgrade().expect("weak reference must be valid");
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}:{}", key, v.1)?;
            first = false;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_with_max_entries() {
        let cache: LruHashMap<(), ()> = LruHashMap::with_max_entries(10);
        assert_eq!(cache.cap(), 10);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_insert_and_get() {
        let mut cache = LruHashMap::with_max_entries(2);
        cache.insert("a", 1);
        cache.insert("b", 2);

        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.get(&"b"), Some(&2));
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_get_mut() {
        let mut cache = LruHashMap::with_max_entries(2);
        cache.insert("a", 1);
        if let Some(v) = cache.get_mut(&"a") {
            *v = 2;
        }
        assert_eq!(cache.get(&"a"), Some(&2));
    }

    #[test]
    fn test_contains_key() {
        let mut cache = LruHashMap::with_max_entries(2);
        cache.insert("a", 1);
        assert!(cache.contains_key(&"a"));
        assert!(!cache.contains_key(&"b"));
    }

    #[test]
    fn test_insert_evicts_lru() {
        let mut cache = LruHashMap::with_max_entries(2);
        cache.insert("a", 1);
        cache.insert("b", 2);
        assert_eq!(cache.insert("c", 3), Some(("a", 1)));
        assert_eq!(cache.get(&"a"), None);
        assert_eq!(cache.get(&"b"), Some(&2));
        assert_eq!(cache.get(&"c"), Some(&3));
    }

    #[test]
    fn test_get_updates_lru_order() {
        let mut cache = LruHashMap::with_max_entries(2);
        cache.insert("a", 1);
        cache.insert("b", 2);
        assert_eq!(cache.get(&"a"), Some(&1)); // "a" is now most recently used
        assert_eq!(cache.insert("c", 3), Some(("b", 2))); // "b" is evicted, not "a"
        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.get(&"b"), None);
        assert_eq!(cache.get(&"c"), Some(&3));
    }

    #[test]
    fn test_remove() {
        let mut cache = LruHashMap::with_max_entries(2);
        cache.insert("a", 1);
        cache.insert("b", 2);
        assert_eq!(cache.remove(&"a"), Some(1));
        assert_eq!(cache.remove(&"b"), Some(2));
        assert_eq!(cache.remove(&"c"), None);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_remove_lru() {
        let mut cache = LruHashMap::with_max_entries(2);
        cache.insert("a", 1);
        cache.insert("b", 2);
        assert_eq!(cache.pop_lru(), Some(("a", 1)));
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.pop_lru(), Some(("b", 2)));
        assert_eq!(cache.pop_lru(), None);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_len_and_is_empty() {
        let mut cache = LruHashMap::with_max_entries(2);
        assert!(cache.is_empty());
        cache.insert("a", 1);
        assert!(!cache.is_empty());
        assert_eq!(cache.len(), 1);
        cache.insert("b", 2);
        assert_eq!(cache.len(), 2);
        cache.remove(&"a");
        assert_eq!(cache.len(), 1);
        cache.remove(&"b");
        assert!(cache.is_empty());
    }

    #[test]
    fn test_insert_updates_existing_key() {
        let mut cache = LruHashMap::with_max_entries(2);
        cache.insert("a", 1);
        cache.insert("a", 2);
        assert_eq!(cache.get(&"a"), Some(&2));
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_lru_order_with_multiple_operations() {
        let mut cache = LruHashMap::with_max_entries(3);
        cache.insert("a", 1);
        cache.insert("b", 2);
        cache.insert("c", 3);
        assert_eq!(cache.get(&"a"), Some(&1)); // "a" is now most recently used
        cache.insert("d", 4); // "b" should be evicted
        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.get(&"b"), None);
        assert_eq!(cache.get(&"c"), Some(&3));
        assert_eq!(cache.get(&"d"), Some(&4));
    }

    #[test]
    fn test_remove_lru_after_get() {
        let mut cache = LruHashMap::with_max_entries(3);
        cache.insert("a", 1);
        cache.insert("b", 2);
        cache.insert("c", 3);
        assert_eq!(cache.get(&"a"), Some(&1)); // "a" is now most recently used
        assert_eq!(cache.pop_lru(), Some(("b", 2))); // "b" is the LRU
        assert_eq!(cache.len(), 2);
        assert_eq!(cache.get(&"a"), Some(&1));
        assert_eq!(cache.get(&"c"), Some(&3));
    }

    #[test]
    fn test_iter_forward() {
        let mut cache = LruHashMap::with_max_entries(3);
        cache.insert("a", 1);
        cache.insert("b", 2);
        cache.insert("c", 3);

        // Access "a" to make it the most recently used
        assert_eq!(cache.get(&"a"), Some(&1));

        let mut iter = cache.items();
        // Should iterate from most recently used ("a") to least recently used ("b")
        assert_eq!(iter.next(), Some((Rc::new("a"), &1)));
        assert_eq!(iter.next(), Some((Rc::new("c"), &3)));
        assert_eq!(iter.next(), Some((Rc::new("b"), &2)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_backward() {
        let mut cache = LruHashMap::with_max_entries(3);
        cache.insert("a", 1);
        cache.insert("b", 2);
        cache.insert("c", 3);

        // Access "a" to make it the most recently used
        assert_eq!(cache.get(&"a"), Some(&1));

        let mut iter = cache.items();
        // Should iterate backward from least recently used ("b") to most recently used ("a")
        assert_eq!(iter.next_back(), Some((Rc::new("b"), &2)));
        assert_eq!(iter.next_back(), Some((Rc::new("c"), &3)));
        assert_eq!(iter.next_back(), Some((Rc::new("a"), &1)));
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_iter_mixed_direction() {
        let mut cache = LruHashMap::with_max_entries(3);
        cache.insert("a", 1);
        cache.insert("b", 2);
        cache.insert("c", 3);

        // Access "a" to make it the most recently used
        assert_eq!(cache.get(&"a"), Some(&1));

        let mut iter = cache.items();
        // Forward
        assert_eq!(iter.next(), Some((Rc::new("a"), &1)));
        // Backward
        assert_eq!(iter.next_back(), Some((Rc::new("b"), &2)));
        // Forward again
        assert_eq!(iter.next(), Some((Rc::new("c"), &3)));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_keys_iter_forward() {
        let mut cache = LruHashMap::with_max_entries(3);
        cache.insert("a", 1);
        cache.insert("b", 2);
        cache.insert("c", 3);

        // Access "a" to make it the most recently used
        assert_eq!(cache.get(&"a"), Some(&1));

        let mut keys = cache.keys();
        assert_eq!(keys.next(), Some(Rc::new("a")));
        assert_eq!(keys.next(), Some(Rc::new("c")));
        assert_eq!(keys.next(), Some(Rc::new("b")));
        assert_eq!(keys.next(), None);
    }

    #[test]
    fn test_keys_iter_backward() {
        let mut cache = LruHashMap::with_max_entries(3);
        cache.insert("a", 1);
        cache.insert("b", 2);
        cache.insert("c", 3);

        // Access "a" to make it the most recently used
        assert_eq!(cache.get(&"a"), Some(&1));

        let mut keys = cache.keys();
        assert_eq!(keys.next_back(), Some(Rc::new("b")));
        assert_eq!(keys.next_back(), Some(Rc::new("c")));
        assert_eq!(keys.next_back(), Some(Rc::new("a")));
        assert_eq!(keys.next_back(), None);
    }

    #[test]
    fn test_values_iter_forward() {
        let mut cache = LruHashMap::with_max_entries(3);
        cache.insert("a", 1);
        cache.insert("b", 2);
        cache.insert("c", 3);

        // Access "a" to make it the most recently used
        assert_eq!(cache.get(&"a"), Some(&1));

        let mut values = cache.values();
        assert_eq!(values.next(), Some(&1));
        assert_eq!(values.next(), Some(&3));
        assert_eq!(values.next(), Some(&2));
        assert_eq!(values.next(), None);
    }

    #[test]
    fn test_values_iter_backward() {
        let mut cache = LruHashMap::with_max_entries(3);
        cache.insert("a", 1);
        cache.insert("b", 2);
        cache.insert("c", 3);

        // Access "a" to make it the most recently used
        assert_eq!(cache.get(&"a"), Some(&1));

        let mut values = cache.values();
        assert_eq!(values.next_back(), Some(&2));
        assert_eq!(values.next_back(), Some(&3));
        assert_eq!(values.next_back(), Some(&1));
        assert_eq!(values.next_back(), None);
    }

    #[test]
    fn test_empty_iter() {
        let cache: LruHashMap<&str, i32> = LruHashMap::with_max_entries(3);
        let mut iter = cache.items();
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }
}
