#include <mutex>
#include <atomic>
#include <iostream>
#include <ctime>
#include <thread>
#include <condition_variable>
#include <queue>
#include <functional>
#include <cassert>

const int LOOPS_COUNT = 10;
const int TREE_DEPTH =20;

using std::queue;
using std::vector;
using std::pair;

template<typename Counter>
struct Resource {
	Counter counter = 0;

	virtual ~Resource() = default;
	inline void retain() { counter++; }
	inline void release() {
		if (--counter == 0)
			delete this;
	}
	inline void st_release() { release();  }
	using ThreadGuard = int;
	static void start(std::function<void()> root_mutator) { root_mutator(); }
};

using SingleThreadedResource = Resource<size_t>;
using MultiThreadedResource = Resource<std::atomic<size_t>>;

struct DelayedResource {
	struct Page {
		const static size_t size = 4096;
		static size_t generator;
		size_t start_gen;
		size_t end_gen;
		DelayedResource* buffer[size];
		DelayedResource** incs;
		DelayedResource** decs;
		static thread_local Page* thread_own;
		static std::mutex mutex;
		static std::condition_variable cvar;
		static queue<Page*> gen_queue; // pages to be processed ordered by start_gen.
		static queue<size_t> check_queue; // gen|1 or PtrToResource|0
		static vector<DelayedResource*> to_delete;
		static vector<Page*> pool;

		void init() {
			end_gen = 0;
			start_gen = generator += 2;
			incs = buffer;
			decs = buffer + size;
			gen_queue.push(this);
			thread_own = this;
		}
		void inc(DelayedResource* r) {
			*incs = r;
			if (++incs == decs)
				flush();
		}
		void dec(DelayedResource* r) {
			*--decs = r;
			if (incs == decs)
				flush();
		}
		void flush(){
			const std::lock_guard<std::mutex> lock(mutex);
			end_gen = generator;
			set_next_page();
			if (gen_queue.front()->end_gen)
				cvar.notify_one();
		}
		static void set_next_page() {
			if (pool.empty()) {
				(new Page)->init();
			}
			else {
				pool.back()->init();
				pool.pop_back();
			}
		}
		void execute() {
			check_queue.push(end_gen);
			for (DelayedResource** i = incs; --i >= buffer;) {
				auto& ct = (*i)->counter;
				if (ct & 1)
					ct = 2;
				else if ((ct += 2) == 0) {
					ct = end_gen;
					check_queue.push((size_t)*i);
				}
			}
			for (DelayedResource** i = decs; i < buffer + size; i++) {
				auto& ct = (*i)->counter;
				if (ct & 1)
					ct = -2;
				else if ((ct -= 2) == 0) {
					ct = end_gen;
					check_queue.push((size_t)*i);
				}
			}
			size_t g = 0;
			for (; !check_queue.empty(); check_queue.pop()) {
				auto i = check_queue.front();
				if (i & 1) {
					if ((i - start_gen) & (~(~0u >> 1)))
						break;
					g = i;
				} else if (((DelayedResource*)i)->counter == g) {
					to_delete.push_back((DelayedResource*)i);
					((DelayedResource*)i)->counter = 0;
				}
			}
			if (!to_delete.empty()) {
				for (auto i : to_delete)
					delete i;
				to_delete.clear();
			}
		}
	};
	struct ThreadGuard {
		ThreadGuard() {
			Page::set_next_page();
		}
		~ThreadGuard() {
			if (Page::thread_own) {
				const std::lock_guard<std::mutex> lock(Page::mutex);
				Page::thread_own->end_gen = Page::generator;
				if (Page::gen_queue.front()->end_gen)
					Page::cvar.notify_one();
			}
		}
	};
	// nnnn1 -> to be deleted in gen nnnn
	// vvvv0 -> counter with signed overflow
	size_t counter = 0;

	virtual ~DelayedResource() = default;

	void retain() { Page::thread_own->inc(this); }
	void release() { Page::thread_own->dec(this); }
	inline void st_release() {
		if ((counter -= 2) == 0)
			delete this;
	}
	static void flush() {
		Page::thread_own->flush();
	}
	static void start(std::function<void()> root_mutator) {
		std::thread t([&] {
			ThreadGuard guard;
			root_mutator();
			Page::cvar.notify_one();
		});
		{
			std::unique_lock<std::mutex> lock(Page::mutex);
			for (;;) {
				Page::cvar.wait(lock);
				for (;;) {
					if (Page::gen_queue.empty()) {
						assert(Page::check_queue.empty());
						t.join();
						return;
					}
					auto p = Page::gen_queue.front();
					if (!p->end_gen)
						break;
					Page::gen_queue.pop();
					if (Page::gen_queue.size() > 10) {
						p->execute();
					} else {
						lock.unlock();
						p->execute();
						lock.lock();
					}
					Page::pool.push_back(p);
				}
			}
		}
	}
};

std::mutex DelayedResource::Page::mutex;
size_t DelayedResource::Page::generator = 1;
thread_local DelayedResource::Page* DelayedResource::Page::thread_own;
std::condition_variable DelayedResource::Page::cvar;
queue<DelayedResource::Page*> DelayedResource::Page::gen_queue;
queue<size_t> DelayedResource::Page::check_queue; // gen|1 or PtrToResource|0
vector<DelayedResource::Page*> DelayedResource::Page::pool;
vector<DelayedResource*> DelayedResource::Page::to_delete;

template <typename R>
struct local;
template <typename R>
struct field;

template <typename R>
struct local {
	R* r;

	local(nullptr_t) :r() {}
	local(R* src = nullptr) :r(src) {
		if (r)
			r->retain();
	}
	local(const local& src) : local(src.r) {}
	local(const field<R>& src) : local(src.r) {}
	~local() {
		if (r)
			r->release();
	}
	operator bool() { return r != nullptr;  }
	local<R>& operator= (R* src) {
		if (src)
			src->retain();
		if (r)
			r->release();
		r = src;
		return *this;
	}
	local<R>& operator= (const local& src) { return this->operator=(src.r); }
	local<R>& operator= (const field<R>& src) { return this->operator=(src.r); }
	R* operator->() { return r; }
};
template <typename R>
struct field {
	R* r;

	field(nullptr_t) :r() {}
	field(R* src = nullptr) :r(src) {
		if (r)
			r->retain();
	}
	field(const field& src) : field(src.r) {}
	field(const local<R>& src) : field(src.r) {}
	~field() {
		if (r)
			r->st_release();
	}
	operator bool() { return r != nullptr; }
	field<R>& operator= (R* src) {
		if (src)
			src->retain();
		if (r)
			r->release();
		r = src;
		return *this;
	}
	field<R>& operator= (const field& src) { return this->operator=(src.r); }
	field<R>& operator= (const local<R>& src) { return this->operator=(src.r); }
	R* operator->() { return r; }
};

std::atomic<int> alive = 0;
// int alive = 0;
template<typename Base>
struct TestObject : Base {
	field<TestObject<Base>> left, right;
	int data;

	TestObject(int d) : data(d) { alive++; }
	~TestObject() { alive--; }
};

template<typename R>
void fill(local<TestObject<R>> dst, int depth) {
	if (depth >= TREE_DEPTH)
		return;
	dst->left = new TestObject<R>(depth);
	fill<R>(dst->left, depth + 1);
	dst->right = new TestObject<R>(depth + 1);
	fill<R>(dst->right, depth + 1);
}

template<typename R>
int process(local<TestObject<R>> dst) {
	return dst ? dst->data + process<R>(dst->left) + process<R>(dst->right) : 0;
}

template<typename R>
void perform_test(bool mt, const char* name) {
	R::start([&] {
		auto start_time = std::clock();
		int r = 0;
		for (int i = LOOPS_COUNT; --i >= 0;) {
			local<TestObject<R>> root = new TestObject<R>(0);
			fill(root, 0);
			if (mt) {
				int tr;
				std::thread t([&] {
					typename R::ThreadGuard guard;
					tr = process(root);
					});
				r += process(root);
				t.join();
			}
			else {
				r += process(root);
			}
		}
		std::cout
			<< name << ": (" << alive << ") "
			<< " result = " << r
			<< " takes:" << ((std::clock() - start_time) / (CLOCKS_PER_SEC / 1000))
			<< std::endl;
	});
}

int main() {
	for (;;) {
		perform_test<SingleThreadedResource>(false, "unsafe");
		perform_test<MultiThreadedResource>(false, "atomic");
		perform_test<MultiThreadedResource>(true, "atomic-mt");
		perform_test<DelayedResource>(false, "delayed");
		perform_test<DelayedResource>(true, "delayed-mt");
	}
	return 0;
}
