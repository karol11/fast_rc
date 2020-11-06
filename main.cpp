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
const int TREE_DEPTH = 20;

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
	struct Task;
	static const size_t size = 4096;
	static size_t generator;
	static thread_local Task* thread_own;
	static std::mutex mutex;
	static std::condition_variable cvar;
	static queue<Task*> task_queue;
	static queue<size_t> nom_queue;
	static vector<DelayedResource*> to_delete;
	static vector<Task*> pool;
	static size_t tagged_gen;

	enum {
		PTR = 0b00,
		TAG = 0b01,
		INCOMPLETE = 0b10,
		COMPLETE = 0b11,
	};
	struct Task {
		size_t* gen_ptr;
		size_t start_gen;
		DelayedResource* buffer[size];
		DelayedResource** incs;
		DelayedResource** decs;

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
		void process() {
			tagged_gen = 0;
			for (DelayedResource** i = incs; --i >= buffer;) {
				auto& ct = (*i)->counter;
				if (ct & 1)
					ct = 4;
				else if ((ct += 4) == 0) {
					if (!tagged_gen) {
						tagged_gen = start_gen | TAG;
						nom_queue.push(tagged_gen);
					}
					ct = tagged_gen;
					nom_queue.push((size_t)*i);
				}
			}
			for (DelayedResource** i = decs; i < buffer + size; i++) {
				auto& ct = (*i)->counter;
				if (ct & 1)
					ct = -4;
				else if ((ct -= 4) == 0) {
					if (!tagged_gen) {
						tagged_gen = start_gen | TAG;
						nom_queue.push(tagged_gen);
					}
					ct = tagged_gen;
					nom_queue.push((size_t)*i);
				}
			}
			*gen_ptr |= COMPLETE;
			handle_nominated();
		}
		static void handle_nominated() {
			size_t tag = 0;
			while (!nom_queue.empty()) {
				auto n = nom_queue.front();
				switch (n & 3) {
				case INCOMPLETE: return;
				case COMPLETE: break;
				case TAG: tag = n; break;
				default:
				{
					auto* p = (DelayedResource*)n;
					if (p->counter == tag) {
						to_delete.push_back(p);
						p->counter = 0;
					}
				}
				}
				nom_queue.pop();
			}
		}
		static void flush(){
			Task* t;
			{
				const std::lock_guard<std::mutex> lock(mutex);
				if (thread_own)
					task_queue.push(thread_own);
				if (pool.empty())
					t = new Task;
				else {
					t = pool.back();
					pool.pop_back();
				}
				t->gen_ptr = nullptr;
				task_queue.push(t);
			}
			t->incs = t->buffer;
			t->decs = t->buffer + size;
			thread_own = t;
			cvar.notify_one();
		}
	};
	struct ThreadGuard {
		ThreadGuard() {
			Task::flush();
		}
		~ThreadGuard() {
			if (thread_own) {
				const std::lock_guard<std::mutex> lock(mutex);
				task_queue.push(thread_own);
				thread_own = nullptr;
				cvar.notify_one();
			}
		}
	};
	size_t counter = 0;

	virtual ~DelayedResource() = default;

	inline void retain() { thread_own->inc(this); }
	inline void release() { thread_own->dec(this); }
	inline void st_release() {
		if (counter & 1)
			counter = -4;
		else if ((counter -= 4) == 0) {
			if (!tagged_gen) {
				tagged_gen = (generator += 4) | TAG;
				nom_queue.push(tagged_gen);
			}
			counter = tagged_gen;
			nom_queue.push((size_t)this);
		}
	}
	static void flush() { thread_own->flush(); }
	static void start(std::function<void()> root_mutator) {
		std::thread root_thread([&] {
			{
				ThreadGuard guard;
				root_mutator();
			}
			task_queue.push(nullptr);
			cvar.notify_one();
		});
		std::unique_lock<std::mutex> lock(mutex);
		for (;;) {
			cvar.wait(lock, [] { return!task_queue.empty(); });
			Task* t;
			do {
				t = task_queue.front();
				task_queue.pop();
				if (!t)
					break;
				if (!t->gen_ptr) {
					t->start_gen = generator += 4;
					nom_queue.push(t->start_gen | INCOMPLETE);
					t->gen_ptr = &nom_queue.back();
				} else {
					lock.unlock();
					t->process();
					lock.lock();
					pool.push_back(t);
				}
			} while (!task_queue.empty());
			while (!to_delete.empty()) {
				lock.unlock();
				tagged_gen = 0;
				for (auto i : to_delete)
					delete i;
				to_delete.clear();
				Task::handle_nominated();
				lock.lock();
			}
			if (!t) {
				root_thread.join();
				assert(task_queue.empty());
				assert(nom_queue.empty());
				assert(to_delete.empty());
				return;
			}
		}
	}
};

std::mutex DelayedResource::mutex;
size_t DelayedResource::generator = 0;
thread_local DelayedResource::Task* DelayedResource::thread_own;
std::condition_variable DelayedResource::cvar;
queue<DelayedResource::Task*> DelayedResource::task_queue;
queue<size_t> DelayedResource::nom_queue;
vector<DelayedResource::Task*> DelayedResource::pool;
vector<DelayedResource*> DelayedResource::to_delete;
size_t DelayedResource::tagged_gen = 0;

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
