// This benchmark file was AI-generated and has not been extensively reviewed.
// It compares the custom Vec-based DoublyLinkedList implementation with std::collections::LinkedList.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use lru_st::DoublyLinkedList;
use rand::prelude::*;
use std::collections::LinkedList;

fn benchmark_push_front(c: &mut Criterion) {
    let mut group = c.benchmark_group("push_front");

    for size in [100, 1000, 10_000].iter() {
        group.bench_with_input(BenchmarkId::new("DoublyLinkedList", size), size, |b, &s| {
            b.iter(|| {
                let mut dll = DoublyLinkedList::with_capacity(s);
                for i in 0..s {
                    dll.push_front(black_box(i));
                }
                black_box(dll)
            })
        });

        group.bench_with_input(BenchmarkId::new("std::LinkedList", size), size, |b, &s| {
            b.iter(|| {
                let mut list = LinkedList::new();
                for i in 0..s {
                    list.push_front(black_box(i));
                }
                black_box(list)
            })
        });
    }

    group.finish();
}

fn benchmark_push_back(c: &mut Criterion) {
    let mut group = c.benchmark_group("push_back");

    for size in [100, 1000, 10_000].iter() {
        group.bench_with_input(BenchmarkId::new("DoublyLinkedList", size), size, |b, &s| {
            b.iter(|| {
                let mut dll = DoublyLinkedList::with_capacity(s);
                for i in 0..s {
                    dll.push_back(black_box(i));
                }
                black_box(dll)
            })
        });

        group.bench_with_input(BenchmarkId::new("std::LinkedList", size), size, |b, &s| {
            b.iter(|| {
                let mut list = LinkedList::new();
                for i in 0..s {
                    list.push_back(black_box(i));
                }
                black_box(list)
            })
        });
    }

    group.finish();
}

fn benchmark_pop_front(c: &mut Criterion) {
    let mut group = c.benchmark_group("pop_front");

    for size in [100, 1000, 10_000].iter() {
        group.bench_with_input(BenchmarkId::new("DoublyLinkedList", size), size, |b, &s| {
            b.iter(|| {
                let mut dll = DoublyLinkedList::with_capacity(s);
                for i in 0..s {
                    dll.push_back(black_box(i));
                }
                for _ in 0..s {
                    let _ = dll.pop_front();
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("std::LinkedList", size), size, |b, &s| {
            b.iter(|| {
                let mut list = LinkedList::new();
                for i in 0..s {
                    list.push_back(black_box(i));
                }
                for _ in 0..s {
                    let _ = list.pop_front();
                }
            })
        });
    }

    group.finish();
}

fn benchmark_pop_back(c: &mut Criterion) {
    let mut group = c.benchmark_group("pop_back");

    for size in [100, 1000, 10_000].iter() {
        group.bench_with_input(BenchmarkId::new("DoublyLinkedList", size), size, |b, &s| {
            b.iter(|| {
                let mut dll = DoublyLinkedList::with_capacity(s);
                for i in 0..s {
                    dll.push_front(black_box(i));
                }
                for _ in 0..s {
                    let _ = dll.pop_back();
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("std::LinkedList", size), size, |b, &s| {
            b.iter(|| {
                let mut list = LinkedList::new();
                for i in 0..s {
                    list.push_front(black_box(i));
                }
                for _ in 0..s {
                    let _ = list.pop_back();
                }
            })
        });
    }

    group.finish();
}

fn benchmark_iter_forward(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter_forward");

    for size in [100, 1000, 10_000, 100_000].iter() {
        let dll_data: Vec<usize> = (0..*size).collect();
        let std_data: Vec<usize> = (0..*size).collect();

        group.bench_with_input(
            BenchmarkId::new("DoublyLinkedList", size),
            size,
            |b, &_s| {
                let dll: DoublyLinkedList<_> = dll_data.iter().cloned().collect();
                b.iter(|| {
                    let mut sum = 0usize;
                    for v in dll.iter() {
                        sum = sum.wrapping_add(*v);
                    }
                    black_box(sum)
                })
            },
        );

        group.bench_with_input(BenchmarkId::new("std::LinkedList", size), size, |b, &_s| {
            let list: LinkedList<usize> = std_data.clone().into_iter().collect();
            b.iter(|| {
                let mut sum = 0usize;
                for v in list.iter() {
                    sum = sum.wrapping_add(*v);
                }
                black_box(sum);
            })
        });
    }

    group.finish();
}

fn benchmark_iter_backward(c: &mut Criterion) {
    let mut group = c.benchmark_group("iter_backward");

    for size in [100, 1000, 10_000, 100_000].iter() {
        let dll_data: Vec<usize> = (0..*size).collect();
        let std_data: Vec<usize> = (0..*size).collect();

        group.bench_with_input(
            BenchmarkId::new("DoublyLinkedList", size),
            size,
            |b, &_s| {
                let dll: DoublyLinkedList<_> = dll_data.iter().cloned().collect();
                b.iter(|| {
                    let mut sum = 0usize;
                    for v in dll.iter().rev() {
                        sum = sum.wrapping_add(*v);
                    }
                    black_box(sum)
                })
            },
        );

        group.bench_with_input(BenchmarkId::new("std::LinkedList", size), size, |b, &_s| {
            let list: LinkedList<usize> = std_data.clone().into_iter().collect();
            b.iter(|| {
                let mut sum = 0usize;
                for v in list.iter().rev() {
                    sum = sum.wrapping_add(*v);
                }
                black_box(sum);
            })
        });
    }

    group.finish();
}

fn benchmark_get_by_cursor(c: &mut Criterion) {
    let mut group = c.benchmark_group("get_by_cursor");

    for size in [100, 1000, 10_000].iter() {
        group.bench_with_input(BenchmarkId::new("DoublyLinkedList", size), size, |b, &s| {
            let mut dll = DoublyLinkedList::with_capacity(s);
            let mut cursors = Vec::with_capacity(s);
            for i in 0..s {
                cursors.push(dll.push_back(i));
            }
            b.iter(|| {
                let mut sum = 0usize;
                for &cursor in &cursors {
                    sum = sum.wrapping_add(*dll.get(black_box(cursor)).unwrap());
                }
                black_box(sum)
            })
        });
    }

    group.finish();
}

fn benchmark_move_front(c: &mut Criterion) {
    let mut group = c.benchmark_group("move_front");

    for size in [100, 1000, 10_000].iter() {
        group.bench_with_input(BenchmarkId::new("DoublyLinkedList", size), size, |b, &s| {
            b.iter(|| {
                let mut dll = DoublyLinkedList::with_capacity(s);
                let mut cursors = Vec::with_capacity(s);
                for i in 0..s {
                    cursors.push(dll.push_back(i));
                }
                for &cursor in &cursors {
                    let _ = dll.move_front(black_box(cursor));
                }
            })
        });
    }

    group.finish();
}

fn benchmark_random_access(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_access_iter_nth");

    for size in [100, 1000, 10_000].iter() {
        let dll: DoublyLinkedList<_> = (0..*size).collect();
        let std_list: LinkedList<usize> = (0..*size).collect();

        let mut rng = thread_rng();
        let indices: Vec<usize> = (0..*size).map(|_| rng.gen_range(0..*size)).collect();

        group.bench_with_input(
            BenchmarkId::new("DoublyLinkedList", size),
            size,
            |b, &_s| {
                b.iter(|| {
                    let mut sum = 0usize;
                    for &i in &indices {
                        sum = sum.wrapping_add(*dll.iter().nth(black_box(i)).unwrap());
                    }
                    black_box(sum)
                })
            },
        );

        group.bench_with_input(BenchmarkId::new("std::LinkedList", size), size, |b, &_s| {
            b.iter(|| {
                let mut sum = 0usize;
                for &i in &indices {
                    sum = sum.wrapping_add(*std_list.iter().nth(black_box(i)).unwrap());
                }
                black_box(sum)
            })
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    benchmark_push_front,
    benchmark_push_back,
    benchmark_pop_front,
    benchmark_pop_back,
    benchmark_iter_forward,
    benchmark_iter_backward,
    benchmark_get_by_cursor,
    benchmark_move_front,
    benchmark_random_access,
);

criterion_main!(benches);
