def is_partition_of(partition, n):
    """Check that a list of lists of numbers is a set partition of 1, ..., n."""
    counts = [0] * n
    for s in partition:
        for i in s:
            if not 0 <= i < n:
                raise IndexError("index out of range")
            counts[i] += 1
    return all(count == 1 for count in counts)

def integer_partitions(n, bound=False, length_bound=False, return_increasing=False):
    """
    Generates all integer partitions of n.
    Each partition is a list of positive ints.

    Optional argument 'bound' is an upper bound on the part size.
    Optional argument 'length_bound' is an upper bound on the length number of parts.
    Optional argument 'return_increasing' causes the results to be returned in increasing order
    """
    if n == 0:
        yield []
        return
    
    if bound is False:
        bound = n
    if length_bound is False:
        length_bound = n
    
    if length_bound == 0:
        return
    
    for i in range(1, min(n, bound) + 1):
        # i will be the largest part. Thus all smaller parts have a bound of i.
        for smaller_partition in integer_partitions(n-i, i, length_bound-1, return_increasing):
            if return_increasing:
                yield smaller_partition + [i]
            else:
                yield [i] + smaller_partition

def integer_compositions(n, num_parts):
    """
    Generates all integer partitions of n.
    Each partition is a list of positive ints.

    Optional argument 'bound' is an upper bound on the part size.
    """
    if n == 0:
        yield [0]*num_parts
        return
    
    if num_parts == 0:
        return
    
    for i in range(n+1):
        # i will be the first part. Thus all smaller parts have a bound of i.
        for smaller_composition in integer_compositions(n - i, num_parts - 1):
            yield [i] + smaller_composition

def set_partitions(collection):
    """
    Generates all partitions of a given collection (set or list).
    Each partition is a sorted list of sorted lists (implicitly sorted lexicographically,
    in the order of the starting collection).
    """
    if not collection:
        yield []  # Base case: empty set has one partition (empty list of subsets)
        return

    rest, last = collection[:-1], collection[-1]
    
    # Recursively get partitions of the remaining elements
    for smaller_partition in set_partitions(rest):
        # Option 1: Add the first_element to an existing subset
        for i, subset in enumerate(smaller_partition):
            yield smaller_partition[:i] + [subset + [last]] + smaller_partition[i+1:]

        # Option 2: Create a new singleton subset for the first_element
        yield smaller_partition + [[last]]

def ordered_set_partitions(collection):
    """
    Generates all ordered set partitions of a given collection (set or list).
    Each partition is a list of subsets.
    """
    if not collection:
        yield []  # Base case: empty set has one partition (empty list of subsets)
        return

    rest, last = collection[:-1], collection[-1]
    
    # Recursively get partitions of the remaining elements
    for smaller_partition in ordered_set_partitions(rest):
        # Option 1: Add the first_element to an existing subset
        for i, subset in enumerate(smaller_partition):
            yield smaller_partition[:i] + [subset + [last]] + smaller_partition[i+1:]

        # Option 2: Insert a new singleton subset for the first_element
        for i in range(len(smaller_partition) + 1):
            yield smaller_partition[:i] + [[last]] + smaller_partition[i:]

def multinomial_assignment(keys, vals, val_mults):
    """ Multinomial assignment. 
    keys: list of keys
    vals: list of values
    val_mults: list of Ints

    Generates all dicts assigning keys to values so that vals[i] occurs val_mults[i] times, for all i. """
    if keys == []:
        yield dict()
    for i in range(len(val_mults)):
        if val_mults[i] == 0: continue
        mults_rest = [e for e in val_mults]
        mults_rest[i] -= 1
        for result_rest in multinomial_assignment(keys[1:], vals, mults_rest):
            yield {keys[0]:vals[i]} | result_rest
