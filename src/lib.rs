use std::{
    fmt::{Debug, Display},
    hash::Hash,
    ptr,
};

pub mod collections;

#[derive(Debug, Clone, Hash, Copy, Eq, PartialEq)]
pub struct Cursor(usize);

pub struct Node<T> {
    prev: Option<Cursor>,
    next: Option<Cursor>,
    value: T,
    free: bool,
}

impl<T> Node<T> {
    fn free(&mut self) {
        self.prev = None;
        self.next = None;
        self.free = true;
    }
}

pub struct DoublyLinkedList<T> {
    // the head of the list
    head: Option<Cursor>,
    // the tail of the list
    tail: Option<Cursor>,
    // list of nodes
    list: Vec<Node<T>>,
    // free list to use for new node insertion
    free: Vec<Cursor>,
}

impl<T> Default for DoublyLinkedList<T> {
    fn default() -> Self {
        DoublyLinkedList {
            head: None,
            tail: None,
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

#[derive(Debug, PartialEq, PartialOrd, Ord, Eq)]
pub enum Error {
    OutOfBound(usize),
    Uaf,
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::OutOfBound(i) => write!(f, "index out of bound: {}", i),
            Error::Uaf => write!(f, "trying to use freed node"),
        }
    }
}

impl<T> DoublyLinkedList<T> {
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        DoublyLinkedList {
            list: Vec::with_capacity(capacity),
            ..Default::default()
        }
    }

    #[inline]
    pub fn from_vec(v: Vec<T>) -> Self {
        let mut d = Self::new();
        for e in v {
            d.push_back(e);
        }
        d
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    fn next_available_cursor(&mut self) -> Cursor {
        self.free.pop().unwrap_or(Cursor(self.list.len()))
    }

    #[inline]
    fn put(&mut self, e: Node<T>, at: Cursor) {
        if at.0 == self.list.len() {
            self.list.push(e);
            return;
        }
        self.list[at.0] = e;
    }

    #[inline]
    pub fn push_front(&mut self, v: T) -> Cursor {
        let cursor = self.next_available_cursor();
        let node = Node {
            prev: None,
            next: self.head,
            value: v,
            free: false,
        };

        // if there is no tail
        if self.tail.is_none() {
            self.tail = Some(cursor);
        }

        // we link the old head (if existing) to the new one
        self.new_prev(self.head, Some(cursor));

        // we insert element at position
        self.put(node, cursor);
        // new head
        self.head = Some(cursor);
        cursor
    }

    #[inline]
    pub fn push_back(&mut self, v: T) -> Cursor {
        let cursor = self.next_available_cursor();
        // element to be inserted at the end
        let e = Node {
            prev: self.tail,
            next: None,
            value: v,
            free: false,
        };

        // if there is no head we set it
        if self.head.is_none() {
            self.head = Some(cursor);
        }

        // we link the old tail (if existing) to the new one
        self.new_next(self.tail, Some(cursor));

        // we insert element at position
        self.put(e, cursor);
        // new tail
        self.tail = Some(cursor);
        cursor
    }

    #[inline]
    pub fn get(&self, c: Cursor) -> Option<&T> {
        if let Some(e) = self.list.get(c.0) {
            // we return None if node is freed
            if e.free {
                return None;
            }
            return Some(&e.value);
        }
        None
    }

    #[inline]
    pub fn get_mut(&mut self, c: Cursor) -> Option<&mut T> {
        if let Some(e) = self.list.get_mut(c.0) {
            // we return None if node is freed
            if e.free {
                return None;
            }
            return Some(&mut e.value);
        }
        None
    }

    #[inline]
    pub fn front(&self) -> Option<&T> {
        if let Some(c) = self.head {
            return self.get(c);
        }
        None
    }

    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        if let Some(c) = self.head {
            return self.get_mut(c);
        }
        None
    }

    #[inline]
    pub fn back(&self) -> Option<&T> {
        if let Some(c) = self.tail {
            return self.get(c);
        }
        None
    }

    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        if let Some(c) = self.tail {
            return self.get_mut(c);
        }
        None
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.list.len() - self.free.len()
    }

    #[inline]
    fn node_mut(&mut self, at: Cursor) -> Option<&mut Node<T>> {
        self.list.get_mut(at.0)
    }

    #[inline]
    pub fn node(&self, at: Cursor) -> Option<&Node<T>> {
        self.list.get(at.0)
    }

    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        if let Some(tail_curs) = self.tail {
            // should never panic
            let tail = self
                .node_mut(tail_curs)
                .expect("node should be available at tail position");
            // tail must not be freed at this point
            debug_assert!(!tail.free);

            // previous node cursor
            let prev = tail.prev;
            // copy value T to return it
            let out = unsafe { Some(ptr::read(&(tail.value) as *const T)) };
            // we free current node
            tail.free();
            debug_assert!(tail.free);

            // the previous element becomes the new tail
            self.new_next(prev, None);

            // tail is also head
            if prev.is_none() {
                self.head = None
            }

            // we have a new tail
            self.tail = prev;
            // we put available cursor in the free list
            self.free.push(tail_curs);
            return out;
        }
        None
    }

    #[inline]
    fn new_prev(&mut self, at: Option<Cursor>, prev: Option<Cursor>) {
        // if there is something at pos
        if let Some(at) = at {
            // we modify element at pos
            self.list[at.0].prev = prev
        }
    }

    #[inline]
    fn new_next(&mut self, at: Option<Cursor>, next: Option<Cursor>) {
        // if there is something at pos
        if let Some(at) = at {
            // we modify element at pos
            self.list[at.0].next = next;
        }
    }

    #[inline]
    pub fn iter(&self) -> DoublyLinkedListIter<T> {
        DoublyLinkedListIter {
            dll: self,
            front_cursor: self.head,
            back_cursor: self.tail,
            cross: false,
        }
    }

    // move item at cursor to the head of list
    #[inline]
    pub fn move_front(&mut self, at: Cursor) -> Result<(), Error> {
        if at.0 >= self.list.len() {
            return Err(Error::OutOfBound(at.0));
        }

        // we are trying to move a freed node to the top of the list
        if self.list[at.0].free {
            return Err(Error::Uaf);
        }

        // if we are not processing head
        if self.list[at.0].prev.is_some() {
            // we link next to prev
            self.new_prev(self.list[at.0].next, self.list[at.0].prev);
            // we link prev to next
            self.new_next(self.list[at.0].prev, self.list[at.0].next);

            // we are processing the tail so we have to assign a new
            // self.tail
            if self.list[at.0].next.is_none() {
                self.tail = self.list[at.0].prev
            }

            // linking old head to the new head
            self.new_prev(self.head, Some(at));

            // we make item the new head
            self.list[at.0].next = self.head;
            self.list[at.0].prev = None;
            self.head = Some(at);
        }

        Ok(())
    }

    #[inline]
    #[allow(dead_code)]
    fn verify(&self) {
        let mut prev = None;
        let mut oc = self.head;
        while let Some(c) = oc {
            let node = self.list.get(c.0).unwrap();
            // we check back link
            assert_eq!(node.prev, prev);
            prev = Some(c);
            oc = node.next;
        }
    }
}

pub struct DoublyLinkedListIter<'a, T> {
    dll: &'a DoublyLinkedList<T>,
    front_cursor: Option<Cursor>,
    back_cursor: Option<Cursor>,
    cross: bool,
}

impl<'a, T> Iterator for DoublyLinkedListIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.cross {
            return None;
        }

        if self.front_cursor == self.back_cursor {
            self.cross = true
        }

        let cursor = self.front_cursor?;
        let node = self.dll.node(cursor).expect("node must be found at cursor");
        self.front_cursor = node.next;
        Some(&node.value)
    }
}

impl<'a, T> DoubleEndedIterator for DoublyLinkedListIter<'a, T> {
    //type Item = &'a T;
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.cross {
            return None;
        }

        if self.front_cursor == self.back_cursor {
            self.cross = true
        }

        let cursor = self.back_cursor?;
        // nodes pointed by others should always be valid
        let node = self.dll.node(cursor).expect("node must be found at cursor");
        self.back_cursor = node.prev;
        Some(&node.value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
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
        let d = DoublyLinkedList::from_vec(vec![1, 2, 3, 4, 5]);
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
        let d = DoublyLinkedList::from_vec((0..len).collect());

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
            assert_eq!(d.pop_back().unwrap(), i);
            assert!(d.node(Cursor(i)).unwrap().free);
            d.free
                .iter()
                .for_each(|i| assert!(d.node(*i).unwrap().free));
        }

        assert!(d.is_empty());
        assert_eq!(d.head, None);
        assert_eq!(d.tail, None);
        assert_eq!(d.free.len(), len);
        d.list.iter().for_each(|n| assert!(n.free));
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
            assert!(d.node(Cursor(len - i - 1)).unwrap().free);
            d.free
                .iter()
                .for_each(|i| assert!(d.node(*i).unwrap().free));
        }

        assert!(d.is_empty());
        assert_eq!(d.head, None);
        assert_eq!(d.tail, None);
        assert_eq!(d.free.len(), len);
        d.list.iter().for_each(|n| assert!(n.free));
    }

    #[test]
    fn dll_move_front_test() {
        let len = 100;

        let mut d = DoublyLinkedList::new();

        for i in 0..len {
            d.push_front(i);
        }

        for i in (0..len).rev() {
            println!("moving {} to front", d.get(Cursor(i)).unwrap());
            d.move_front(Cursor(i)).unwrap();
            assert_eq!(d.front().unwrap(), &i);
        }
    }
}
