from itertools import product
from involution import *

# Example 6.17 from the paper, constructed using the MDOrdered function.
color_counts617 = [9, 4, 4]
exponents617 = [[1]*6 + [2, 3], [3], []]
hues617 = [[[1], [2], [3], [4], [5, 6], [7], [8]], [[10]], []]
dec617 = { 1:None,  2:5,  3:7,  4:8, 5:1, 6:5, 7:10, 8:7, 9:10,
          10:None, 11:8, 12:3, 13:8,
          14:None, 15:2, 16:10, 17:4}
MD617 = MDOrdered(color_counts617, exponents617, hues617, dec617, index_mode=1)


# Example 6.17 from paper, constructed using explicit ordered pairs.
color_counts617_2 = [9, 4, 4]
exponents617_2 = [[1]*6 + [2, 3], [3], []]
hues617_2 = [[[0], [1], [2], [3], [4, 5], [6], [7]], [[0]], []]
dec617_2 = {(0, 0):(None, None), (0, 1):(0, 4), (0, 2):(0, 6), (0, 3):(0, 7), (0, 4):(0, 0), (0, 5):(0, 4), (0, 6):(1, 0), (0, 7):(0, 6), (0, 8):(1, 0),
            (1, 0):(None, None), (1, 1):(0, 7), (1, 2):(0, 2), (1, 3):(0, 7),
            (2, 0):(None, None), (2, 1):(0, 1), (2, 2):(1, 0), (2, 3):(0, 3)}
MD617_2 = MismatchedDecoration(color_counts617_2, exponents617_2, hues617_2, dec617_2, print_mode='ordered', index_print_mode=1)

# note that MD617 == MD617_2.

# Example 6.22, constructed using the MDOrdered function.
# same color_counts and exponents as MD617 above.
h622 = [[[1], [2], [3], [4], [5, 6], [7], [8]], [[10]], []]
d622 = { 1:None,  2:5,  3:8,  4:8, 5:1, 6:5, 7:10, 8:7, 9:10,
        10:None, 11:8, 12:3, 13:7,
        14:None, 15:2, 16:10, 17:4}
MD622 = MDOrdered(color_counts617, exponents617, h622, d622, index_mode=1)
test_MD622 = h(h(MD622)) # equals MD622! Note: h is a synonym for hue_involution.


color_counts_test = [3, 2, 2]
exponents_test = [[1, 2], [1], []]
MD_test = all_mismatched_decorations(color_counts_test, exponents_test)


# color_counts_smalltest = [6, 3, 3]
# exponents_smalltest = [[1, 2, 3], [3], []]
# smalltest = list(all_mismatched_decorations(color_counts_smalltest, exponents_smalltest))
# all(hue_involution(hue_involution(md)) == md for md in smalltest) # True!

# color_counts_bigtest = [4, 6, 4]
# exponents_bigtest = [[], [1, 1, 1, 2, 3], [3]]
# bigtest = list(all_mismatched_decorations(color_counts_bigtest, exponents_bigtest))
# all(hue_involution(hue_involution(md)) == md for md in bigtest) # takes 14 seconds; True!

def test_involution(color_counts, exponents, return_data=False, return_result=False, print_stats=True):
    """Compute all mismatched decorations and test the hue involution on all of them."""
    
    if print_stats: print(f'testing:\ncolor_counts={color_counts}\nexponents={exponents}')
    data = list(all_mismatched_decorations(color_counts, exponents))
    
    if print_stats: print(f'\nfound {len(data)} mismatched decorations\n'  
          f'\ntesting involution...')
    test_h = [hue_involution(md) for md in data]
    test_hh = [hue_involution(md) for md in test_h]
    invs = Counter(a == b for a, b in zip(data, test_hh))
    counts = Counter(a == b for a, b in zip(data, test_h))
    signs = Counter(a.sign() for a, b in zip(data, test_h) if a == b)

    if print_stats: print(f'\ninvolution points: {invs[True]} out of {len(data)} satisfy f(f(D)) == D'  
                    f'\n           counts: {counts[True]} fixed, {counts[False]} with f(D) ≠ D'  
                    f'\nfixed point signs: {signs[1]} with sign +1')

    output = []
    if return_data:
        output.append(data)

    flag = invs[True] == len(data)
    if not flag:
        print("DANGER! INVOLUTION FAILED. Are exponents in increasing order?")
    if return_result:
        output.append(flag)
    
    if output is not []:
        return output
        
def all_ones(color_counts, return_data=False):
    """Test [1, 1, 1, color_counts] with one of each psi class excluding the first three colors."""

    cs = [1]*3 + color_counts
    exponents = [[]]*3 + [[1]*c for c in color_counts]
    data = test_involution(cs, exponents, return_data)
    if return_data:
        return data


def one_color(exponents, return_data=False):
    """Test [a, b, 1] with exponents all in the first color.
    Note: a = len(exponents) since in this case every point must be boxed.
        a+b+1 = n = sum(exponents) + 3, so b = sum(exponents) - len(exponents) + 2
    """

    color_counts = [len(exponents), sum(exponents) - len(exponents) + 2, 1]
    es = [exponents, [], []]
    data = test_involution(color_counts, es, return_data)
    if return_data:
        return data
    
def one_color_tall(exponents, return_data=False):
    """Test [a, 1, ..., 1] with exponents all in the first color.
    This is the heavy-light space with all exponents in the light color.
    Note: a = len(exponents) since in this case every point must be boxed.
        a+1+...+1 = n = sum(exponents) + 3, so the number of 1s is = sum(exponents) - len(exponents) + 3
    """

    color_counts = [len(exponents)] + [1]*(sum(exponents) - len(exponents) + 3)
    es = [exponents] + [[]]*(sum(exponents) - len(exponents) + 3)
    data = test_involution(color_counts, es, return_data)
    if return_data:
        return data


def _count_tests(num_points):
    """Helper function for test_all below.
    Counts the number of tests needed (color and exponent counts) for the test_all function.
    In other words, the number of different sets of MismatchedDecorations."""

    if num_points < 3:
        raise ValueError("num_points must be at least 3")

    num_tests = 0
    for color_counts in integer_partitions(num_points):
        if len(color_counts) < 3:
            continue
        for exponents_by_color in integer_compositions(num_points - 3, len(color_counts)):
            num_tests += \
                len(list(product(*(integer_partitions(e, bound=False, length_bound=c)
                                   for c, e in zip(color_counts, exponents_by_color))))
    return num_tests
    
    
def test_all(num_points, print_stats=False, print_conclusions=True, skip_until=0):
    """Test every possible involution on an n-pointed space.
    
    num_points:         the number of marked points
    print_stats:        whether to print statistics on the hue involution (e.g. number of fixed points) during each test
    print_conclusions:  whether to print summary statistics at the end
    skip_until:         use this to resume an interrupted test. this says to skip the first N tests.
                        (the tests are generated in a deterministic order.)
    """

    if num_points < 3:
        raise ValueError("num_points must be at least 3")

    num_tests = 0
    total_MDs = 0
    largest_MDs = 0

    print(f'\nTesting all possible psi class products with n={num_points} marked points'  
          f'\nand color multiplicities sorted in descending order, but no other constraints.')
    N = _count_tests(num_points) # preparatory: count the number of tests to do
    print(f'\nThis will test a total of {N} different sets of MismatchedDecorations.', end='')

    cc_count = 0
    total_cc_count = len(list(x for x in integer_partitions(num_points) if len(x) >= 3))
    for color_counts in integer_partitions(num_points):
        if len(color_counts) < 3:
            continue
        cc_count += 1
        print(f'\n\ncurrent color counts ({cc_count} of {total_cc_count}): {color_counts}'  
              f'\nnumber of tests in this count: {len(list(integer_compositions(num_points - 3, len(color_counts))))}\n')
        for exponents_by_color in integer_compositions(num_points - 3, len(color_counts)):

            for exponents in product(*(integer_partitions(e, bound=False, length_bound=c)
                                       for c, e in zip(color_counts, exponents_by_color))):
                
                num_tests += 1
                print(f'\rCurrently on test #{num_tests} of {N}', end='')
                if num_tests < skip_until: # SKIP TESTS until reaching specified point
                    continue
                data, result = test_involution(color_counts, list(exponents), return_data=True, return_result=True, print_stats=print_stats)
                total_MDs += len(data)
                largest_MDs = max(largest_MDs, len(data))
                if not result:
                    print(f'\n\nBROKE! on test {num_tests}:'  
                          f'\ncolor_counts: {color_counts}'  
                          f'\nexponents: {exponents}')
                    break
    
    if print_conclusions:
        print(f'\n\n{num_tests} tests succeeded!')
        print(f'\n  tested a total of {total_MDs} mismatched decorations')
        print(f'\n  largest set contained {largest_MDs} mismatched decorations')
