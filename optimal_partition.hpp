#pragma once

#include <vector>
#include <algorithm>
#include <iterator>
#include "util.hpp"

#define SINGLE_WINDOW
//#define COARSE_PAR

//#define NO_WINDOW
//#define MULTI_WINDOW

namespace quasi_succinct {

typedef uint32_t posting_t;
typedef uint64_t cost_t;

struct optimal_partition {

	/* what is in partition is pos of docid*/
	std::vector<posting_t> partition;
	// the costs are in bits!
	cost_t cost_opt = 0;

	template<typename ForwardIterator>
	// a window represents the cost of the interval [start, end)
	struct cost_window {

		ForwardIterator start_it;
		ForwardIterator end_it;
		// starting and ending position of the window
		posting_t start = 0;

		// end-th position is not in the current window
		posting_t end = 0;

		// element that precedes the first element of the window
		posting_t min_p = 0;
		posting_t max_p = 0;

		cost_t cost_upper_bound; // The maximum cost for this window

		cost_window(ForwardIterator begin, cost_t cost_upper_bound) :
				start_it(begin), end_it(begin), min_p(*begin), max_p(0), cost_upper_bound(
						cost_upper_bound) {
		}

		uint64_t universe() const {
			return max_p - min_p + 1;
		}

		uint64_t size() const {
			return end - start;
		}

		void advance_start() {
			min_p = *start_it + 1;
			++start;
			++start_it;
		}

		void advance_end() {
			max_p = *end_it;
			++end;
			++end_it;
		}

		// actually we need to skip to the value following
		// the last value of this window, namely 'end'
		void forward_to_end(ForwardIterator endItor, posting_t lastEnd,
				posting_t max) {
			min_p = max + 1;
			max_p = *endItor;

			start_it = endItor;
			end_it = ++endItor;

			start = lastEnd;
			end = lastEnd + 1;
		}
	};

	optimal_partition() {
	}

	template<typename ForwardIterator, typename CostFunction>
	optimal_partition(ForwardIterator begin, uint64_t universe, uint64_t size,
			CostFunction cost_fun, double eps1, double eps2) {

		cost_t single_block_cost = cost_fun(universe, size);
		std::vector<cost_t> min_cost(size + 1, single_block_cost);
		min_cost[0] = 0;

		// create the required window: one for each power of approx_factor
#ifdef MULTI_WINDOW
		std::vector<cost_window<ForwardIterator>> windows;
#else
		std::vector<cost_t> bounds;
#endif
		cost_t cost_lb = cost_fun(1, 1); // minimum cost
		cost_t cost_bound = cost_lb;

		while (eps1 == 0 || cost_bound < cost_lb / eps1) {
#ifdef MULTI_WINDOW
			windows.emplace_back(begin, cost_bound);
#else
			bounds.push_back(cost_bound);
#endif
			if (cost_bound >= single_block_cost)
				break;
			cost_bound = cost_bound * (1 + eps2);
		}

		std::vector<posting_t> path(size + 1, 0);

		/*****************************************/
#ifdef SINGLE_WINDOW
//			posting_t window.start = 0;
//		int loopcount = 0;
		int l = 0;
		cost_t window_cost;
		posting_t nS[bounds.size()];

		cost_window<ForwardIterator> window(begin, 0);
		window.advance_end();

		posting_t last_max_p;
		ForwardIterator last_end_it;

		while (window.end < size) {
			// expand the window
			while (true) {
				window_cost = cost_fun(window.universe(), window.size());

				if (window.end == size) {
					path[window.end] = window.start;
					min_cost[window.end] = min_cost[window.start] + window_cost;
					break;
				}
				if (window_cost >= bounds[l]) {
					nS[l] = window.size();
					if (l > 0 && nS[l - 1] >= 8
							&& nS[l] < nS[l - 1] + nS[l - 1] * eps2) {
						/* exception found! */

#ifdef COARSE_PAR
						// PLAN A: roughly finish the partition to the last end
						path[window.start + nS[l - 1]] = window.start;
						min_cost[window.start + nS[l - 1]] =
						min_cost[window.start]
						+ cost_fun(last_max_p - window.min_p,
								nS[l - 1]);

//						std::cout << window.start + nS[l - 1] << "<-"
//								<< window.start << std::endl;

						window.forward_to_end(last_end_it,
								window.start + nS[l - 1], last_max_p);
#else
						// PLAN B: search for the best partition in the range
						// from last end to current end
						/////////////////////////////////////////////////////
						posting_t pos = window.start + nS[l - 1];
						posting_t minp = window.min_p;
						// set n1 as partition end
						path[pos] = window.start;
						min_cost[pos] = min_cost[window.start]
								+ cost_fun(last_max_p + 1 - window.min_p,
										nS[l - 1]);
						min_cost[window.end] = min_cost[window.start]
								+ window_cost;
						// move the window to n_1
						window.min_p = last_max_p + 1;
						window.start_it = last_end_it;
						window.start = pos;
						// temporary variables preserve best partition
						ForwardIterator tmp_start_it = window.start_it;
						posting_t tmp_min_p = window.min_p;
						posting_t tmp_start = window.start;

						while (window.size() > 1) {
//							loopcount++;
							window_cost = cost_fun(window.universe(),
									window.size());
							min_cost[window.start] = min_cost[pos - nS[l - 1]]
									+ cost_fun(window.min_p - minp,
											nS[l] - window.size());

							if (min_cost[window.start] + window_cost
									< min_cost[window.end]) {

								path[window.start] = pos - nS[l - 1];
								min_cost[window.end] = min_cost[window.start]
										+ window_cost;

								tmp_start_it = window.start_it;
								tmp_min_p = window.min_p;
								tmp_start = window.start;
							}
							window.advance_start();
						}
//						window.forward_to_end(tmp_start_it, tmp_start,
//								tmp_min_p - 1);
						window.min_p = tmp_min_p;
						window.start_it = tmp_start_it;
						window.start = tmp_start;
//						std::cout << window.start << "<-" << pos - nS[l - 1]
//								<< std::endl;
#endif
						/////////////////////////////////////////////////////
						l = 0;
						break;
					}
					l++;

					if (l == bounds.size()) {
						path[window.end] = window.start;
						min_cost[window.end] = min_cost[window.start]
								+ window_cost;

//						std::cout << window.end << "<-" << window.start
//								<< std::endl;

						window.forward_to_end(window.end_it,
								window.start + window.size(), window.max_p);
						l = 0;
						break;
					}
					last_max_p = window.max_p;
					last_end_it = window.end_it;
				}
				window.advance_end();
			}
		}
//		std::cout <<" loopCount: " << loopcount << std::endl;
#endif
		/*****************************************/
#ifdef NO_WINDOW
		//directly compare n(1+eps)
		cost_t window_cost;

		cost_window<ForwardIterator> window(begin, 0);
		window.advance_end();

		while (window.end < size) {

			while (true) {
				window_cost = cost_fun(window.universe(), window.size());
				if (min_cost[window.start] + window_cost
						< min_cost[window.end]) {
					min_cost[window.end] = min_cost[window.start] + window_cost;
					path[window.end] = window.start;
				}
				if (window.end == size)
				break;
				// guarantee the start size is larger than 8
				if (window_cost >= bounds[0] && window.size() > 8)
				break;
				window.advance_end();
			}

			posting_t last_max_p = window.max_p;
			posting_t last_end = window.end;
			ForwardIterator last_end_it = window.end_it;

			while (window_cost < *bounds.end()) {
				last_max_p = window.max_p;
				last_end = window.end;
				last_end_it = window.end_it;

				posting_t n2 =
				window.start + window.size() * (1 + eps2) > size ?
				size :
				window.start
				+ (posting_t) round(
						window.size() * (1 + eps2));
				while (window.end < n2)
				window.advance_end();
				cost_t tmp_window_cost = cost_fun(window.universe(),
						window.size());
				if (tmp_window_cost > window_cost * (1 + eps2)) {
					// exception found!
					// pull back to n1
					path[window.end] = window.start;
					window.forward_to_end(last_end_it, last_end, last_max_p);
					break;
				}
				window_cost = tmp_window_cost;
				if (window.end == size)
				break;
			}
			path[window.end] = window.start;
			window.forward_to_end(last_end_it, last_end, last_max_p);
		}
#endif

#ifdef MULTI_WINDOW
//		int loopcount = 0;
		for (posting_t i = 0; i < size; i++) {
			size_t last_end = i + 1;

			for (auto& window : windows) {

				assert(window.start == i);
				while (window.end < last_end) {
					window.advance_end();
				}

				cost_t window_cost;
				while (true) {
					window_cost = cost_fun(window.universe(), window.size());
					if (min_cost[i] + window_cost < min_cost[window.end]) {
						min_cost[window.end] = min_cost[i] + window_cost;
						path[window.end] = i;
					}
					last_end = window.end;

//					loopcount++;
					if (window.end == size)
					break;
					if (window_cost >= window.cost_upper_bound)
					break;
					window.advance_end();
				}
//				std::cout << "," << last_end << "," << std::endl;
				window.advance_start();
			}
		}
//		std::cout << "u: " << universe << " n: " << size << " windowCount: "
//		<< windows.size() << " loopCount: " << loopcount << std::endl;
#endif
		posting_t curr_pos = size;
		while (curr_pos != 0) {
			partition.push_back(curr_pos);
			curr_pos = path[curr_pos];
		}
		std::reverse(partition.begin(), partition.end());
		cost_opt = min_cost[size];
//		std::cout << "num:" << partition.size() << std::endl;
	}
}
;

}
