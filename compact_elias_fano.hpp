#pragma once

#include <stdexcept>
#include <succinct/bit_vector.hpp>
#include <succinct/broadword.hpp>

#include "global_parameters.hpp"
#include "util.hpp"

namespace quasi_succinct {

    struct compact_elias_fano {

        struct offsets {
            offsets()
            {}

            offsets(uint64_t base_offset,
                    uint64_t universe,
                    uint64_t n,
                    global_parameters const& params)
                : universe(universe)
                , n(n)
            	// unary code中0和1的采样间隔，0表示间隔符，1计数符
                , log_sampling0(params.ef_log_sampling0)
                , log_sampling1(params.ef_log_sampling1)

                , lower_bits(universe > n ? succinct::broadword::msb(universe / n) : 0)
                , mask((uint64_t(1) << lower_bits) - 1)
                  // pad with a zero on both sides as sentinels
                , higher_bits_length(n + (universe >> lower_bits) + 2)
                , pointer_size(ceil_log2(higher_bits_length))
                , pointers0((higher_bits_length - n) >> log_sampling0)  // XXX
                , pointers1(n >> log_sampling1)

                , pointers0_offset(base_offset)
                , pointers1_offset(pointers0_offset + pointers0 * pointer_size)
                , higher_bits_offset(pointers1_offset + pointers1 * pointer_size)
                , lower_bits_offset(higher_bits_offset + higher_bits_length)
                , end(lower_bits_offset + n * lower_bits)
            {
                assert(n > 0);
            }

            uint64_t universe;
            uint64_t n;
            uint64_t log_sampling0;//0的采样间隔
            uint64_t log_sampling1;//1的采样间隔

            uint64_t lower_bits;//表示一个低位所需的位数
            uint64_t mask;//获取低位的掩码
            uint64_t higher_bits_length;//采用unary编码后，所有高位长度的最大值
            uint64_t pointer_size;//高位指针的长度log(higher_bits_length)
            uint64_t pointers0;//间隔符采样点个数(log(u / l) + 2) >> log_sampling0
            uint64_t pointers1;//计数符采样点个数n >> log_sampling1

            uint64_t pointers0_offset;
            uint64_t pointers1_offset;
            uint64_t higher_bits_offset;
            uint64_t lower_bits_offset;
            uint64_t end;
        };

        static QS_FLATTEN_FUNC uint64_t
        bitsize(global_parameters const& params, uint64_t universe, uint64_t n)
        {
            return offsets(0, universe, n, params).end;
        }

        template <typename Iterator>
        static void write(succinct::bit_vector_builder& bvb,
                          Iterator begin,
                          uint64_t universe, uint64_t n,
                          global_parameters const& params)
        {
            using succinct::util::ceil_div;
            uint64_t base_offset = bvb.size();
            offsets of(base_offset, universe, n, params);
            // initialize all the bits to 0
            bvb.zero_extend(of.end - base_offset);

            uint64_t sample1_mask = (uint64_t(1) << of.log_sampling1) - 1;
            uint64_t offset;

            // utility function to set 0 pointers
            // rank_end stands for rank1(end), 即到当前位置1的个数，也就是i
            auto set_ptr0s = [&](uint64_t begin, uint64_t end,
                                 uint64_t rank_end) {
            	//rank_end实际上非0元素的个数，该函记录的是0的位置
            	//最后只会产生u/2^l+2个0，也恰好是指针的个数
                uint64_t begin_zeros = begin - rank_end;//到begin位置0的个数
                uint64_t end_zeros = end - rank_end;//到end位置0的个数

                //end_zeros要大于0的采样数目才会进入for-loop
                for (uint64_t ptr0 = ceil_div(begin_zeros,
                		uint64_t(1) << of.log_sampling0);
                     (ptr0 << of.log_sampling0) < end_zeros;
                     ++ptr0) {
                    if (!ptr0) continue;
                    offset = of.pointers0_offset + (ptr0 - 1) * of.pointer_size;
                    assert(offset + of.pointer_size <= of.pointers1_offset);
                    bvb.set_bits(offset, (ptr0 << of.log_sampling0) + rank_end,
                                 of.pointer_size);
                }
            };

            uint64_t last = 0;
            uint64_t last_high = 0;
            Iterator it = begin;
            for (size_t i = 0; i < n; ++i) {
                uint64_t v = *it++;
                if (i && v < last) {
                    throw std::runtime_error("Sequence is not sorted");
                }
                assert(v < universe);
                // 这里+i+1表示向对应位置插入1，用于计数排序
                uint64_t high = (v >> of.lower_bits) + i + 1;
                uint64_t low = v & of.mask;
                /*写入高位*/
                bvb.set(of.higher_bits_offset + high, 1);

                offset = of.lower_bits_offset + i * of.lower_bits;
                assert(offset + of.lower_bits <= of.end);
                /*写入低位*/
                bvb.set_bits(offset, low, of.lower_bits);

                if (i && (i & sample1_mask) == 0) {
                    uint64_t ptr1 = i >> of.log_sampling1;
                    assert(ptr1 > 0);
                    offset = of.pointers1_offset + (ptr1 - 1) * of.pointer_size;
                    assert(offset + of.pointer_size <= of.higher_bits_offset);
                    /*定长采样高位，注意写入的高位实际上是+i+1之后的*/
                    bvb.set_bits(offset, high, of.pointer_size);
                }

                // write pointers for the run of zeros in [last_high, high)
                set_ptr0s(last_high + 1, high, i);
                last_high = high;
                last = v;
            }

            // pointers to zeros after the last 1
            set_ptr0s(last_high + 1, of.higher_bits_length, n); // XXX
        }

        class enumerator {
        public:

            typedef std::pair<uint64_t, uint64_t> value_type; // (position, value)

            enumerator()
            {}

            enumerator(succinct::bit_vector const& bv, uint64_t offset,
                       uint64_t universe, uint64_t n,
                       global_parameters const& params)
                : m_bv(&bv)
                , m_of(offset, universe, n, params)
                , m_position(size())
                , m_value(m_of.universe)
            {}

            // position's range is [0,n]
            value_type move(uint64_t position)
            {
                assert(position <= m_of.n);

                if (position == m_position) {
                    return value();
                }

                uint64_t skip = position - m_position;
                // optimize small forward skips
                if (QS_LIKELY(position > m_position && skip <= linear_scan_threshold)) {
                    m_position = position;
                    if (QS_UNLIKELY(m_position == size())) {
                        m_value = m_of.universe;
                    } else {
                        succinct::bit_vector::unary_enumerator he = m_high_enumerator;
                        for (size_t i = 0; i < skip; ++i) {
                            he.next();
                        }
                        m_value = ((he.position() - m_of.higher_bits_offset - m_position - 1)
                                   << m_of.lower_bits) | read_low();
                        m_high_enumerator = he;
                    }
                    return value();
                }

                return slow_move(position);
            }

            value_type next_geq(uint64_t lower_bound)
            {
                if (lower_bound == m_value) {
                    return value();
                }

                uint64_t high_lower_bound = lower_bound >> m_of.lower_bits;
                uint64_t cur_high = m_value >> m_of.lower_bits;
                uint64_t high_diff = high_lower_bound - cur_high;

                if (QS_LIKELY(lower_bound > m_value
                              && high_diff <= linear_scan_threshold)) {
                    // optimize small skips
                    next_reader next_value(*this, m_position + 1);
                    uint64_t val;
                    do {
                        m_position += 1;
                        if (QS_LIKELY(m_position < size())) {
                            val = next_value();
                        } else {
                            val = m_of.universe;
                            break;
                        }
                    } while (val < lower_bound);

                    m_value = val;
                    return value();
                } else {
                    return slow_next_geq(lower_bound);
                }
            }

            uint64_t size() const
            {
                return m_of.n;
            }
            /* returns the next value when current position is
             * in the range of 0 to n-1, returns the universe
             * if current position is n */
            value_type next()
            {
                m_position += 1;
                assert(m_position <= size());

                if (QS_LIKELY(m_position < size())) {
                    m_value = read_currentPos();
                } else {
                    m_value = m_of.universe;
                }
                return value();
            }

            /*previous value*/
            uint64_t prev_value() const
            {
                if (m_position == 0) {
                    return 0;
                }

                uint64_t prev_high = 0;
                if (QS_LIKELY(m_position < size())) {
                    prev_high = m_bv->predecessor1(m_high_enumerator.position() - 1);
                } else {
                    prev_high = m_bv->predecessor1(m_of.lower_bits_offset - 1);
                }
                prev_high -= m_of.higher_bits_offset;

                uint64_t prev_pos = m_position - 1;
                uint64_t prev_low =
                    m_bv->get_word56(m_of.lower_bits_offset +
                                     prev_pos * m_of.lower_bits)
                    & m_of.mask;
                return ((prev_high - prev_pos - 1) << m_of.lower_bits) | prev_low;
            }

            uint64_t position() const
            {
                return m_position;
            }

        private:

            value_type QS_NOINLINE slow_move(uint64_t position)
            {
                if (QS_UNLIKELY(position == size())) {
                    m_position = position;
                    m_value = m_of.universe;
                    return value();
                }

                uint64_t skip = position - m_position;
                uint64_t to_skip;
                if (position > m_position
                    && (skip >> m_of.log_sampling1) == 0) {
                    to_skip = skip - 1;
                } else {
                    uint64_t ptr = position >> m_of.log_sampling1;
                    uint64_t high_pos = pointer1(ptr);
                    // 当前指针指向的元素index，也就是目前元素的个数
                    uint64_t high_rank = ptr << m_of.log_sampling1;
                    m_high_enumerator = succinct::bit_vector::unary_enumerator
                        (*m_bv, m_of.higher_bits_offset + high_pos);
                    to_skip = position - high_rank;
                }

                m_high_enumerator.skip(to_skip);
                m_position = position;
                m_value = read_currentPos();
                return value();
            }

            value_type QS_NOINLINE slow_next_geq(uint64_t lower_bound)
            {
                if (QS_UNLIKELY(lower_bound >= m_of.universe)) {
                    return move(size());
                }

                uint64_t high_lower_bound = lower_bound >> m_of.lower_bits;
                uint64_t cur_high = m_value >> m_of.lower_bits;
                uint64_t high_diff = high_lower_bound - cur_high;

                // XXX bounds checking!
                uint64_t to_skip;
                if (lower_bound > m_value
                    && (high_diff >> m_of.log_sampling0) == 0) {
                    // note: at the current position in the bitvector there
                    // should be a 1, but since we already consumed it, it
                    // is 0 in the enumerator, so we need to skip it
                    to_skip = high_diff;
                } else {
                    uint64_t ptr = high_lower_bound >> m_of.log_sampling0;
                    uint64_t high_pos = pointer0(ptr);
                    uint64_t high_rank0 = ptr << m_of.log_sampling0;

                    m_high_enumerator = succinct::bit_vector::unary_enumerator
                        (*m_bv, m_of.higher_bits_offset + high_pos);
                    to_skip = high_lower_bound - high_rank0;
                    // note to_skip starts from ptr
                    // and it is smaller than log_sampling0
                }

                m_high_enumerator.skip0(to_skip);
                m_position = m_high_enumerator.position() - m_of.higher_bits_offset
                    - high_lower_bound;

                next_reader read_value(*this, m_position);
                while (true) {
                    if (QS_UNLIKELY(m_position == size())) {
                        m_value = m_of.universe;
                        return value();
                    }
                    auto val = read_value();
                    if (val >= lower_bound) {
                        m_value = val;
                        return value();
                    }
                    m_position++;
                }
            }

            inline value_type value() const
            {
                return value_type(m_position, m_value);
            }

            inline uint64_t read_low()
            {
                return m_bv->get_word56(m_of.lower_bits_offset
                                        + m_position * m_of.lower_bits)
                    & m_of.mask;
            }

            /* 因为m_position在此函数并未被调整，实际上它并不是读取的next
             * 而是返回当前m_position下的元素值 */
            inline uint64_t read_currentPos()
            {
                assert(m_position < size());
                // m_position即代表当前index下counter（1）的个数
                // high则是当前index在整个高位序列上的偏移，由于码字从0开始，故还要-1
                uint64_t high = m_high_enumerator.next() - m_of.higher_bits_offset;
                return ((high - m_position - 1) << m_of.lower_bits) | read_low();
            }

            struct next_reader {
                next_reader(enumerator& e, uint64_t position)
                    : e(e)
                    , high_enumerator(e.m_high_enumerator)
                    , high_base(e.m_of.higher_bits_offset + position + 1)
                    , lower_bits(e.m_of.lower_bits)
                    , lower_base(e.m_of.lower_bits_offset + position * lower_bits)
                    , mask(e.m_of.mask)
                    , bv(*e.m_bv)
                {}

                ~next_reader()
                {
                    e.m_high_enumerator = high_enumerator;
                }

                uint64_t operator()()
                {
                	// high_base即为高位起始加上position（1的个数）+1
                	// high就是高位的码字了
                    uint64_t high = high_enumerator.next() - high_base;
                    uint64_t low = bv.get_word56(lower_base) & mask;
                    high_base += 1;
                    lower_base += lower_bits;
                    return (high << lower_bits) | low;
                }

                enumerator& e;
                succinct::bit_vector::unary_enumerator high_enumerator;
                uint64_t high_base, lower_bits, lower_base, mask;
                succinct::bit_vector const& bv;
            };

            inline uint64_t pointer(uint64_t offset, uint64_t i) const
            {
                if (i == 0) {
                    return 0;
                } else {
                    return
                        m_bv->get_word56(offset + (i - 1) * m_of.pointer_size)
                        & ((uint64_t(1) << m_of.pointer_size) - 1);
                }
            }

            /* i is geq 1
             * returns the value (position) pointed by i-th pointer0*/
            inline uint64_t pointer0(uint64_t i) const
            {
                return pointer(m_of.pointers0_offset, i);
            }

            /* i is geq 1
             * returns the value (position) pointed by i-th pointer1*/
            inline uint64_t pointer1(uint64_t i) const
            {
                return pointer(m_of.pointers1_offset, i);
            }

            static const uint64_t linear_scan_threshold = 8;

            succinct::bit_vector const* m_bv;
            offsets m_of;

            uint64_t m_position;
            uint64_t m_value;
            succinct::bit_vector::unary_enumerator m_high_enumerator;
        };

    };
}
