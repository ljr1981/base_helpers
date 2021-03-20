note
	description: "Sorted version of a HASH_TABLE"
	ca_ignore: "CA029"

class
	SORTED_HASH [G -> COMPARABLE, K -> detachable HASHABLE]

inherit
	HASH_TABLE [G, K]

create
	make,
	make_equal

feature -- Queries

	i_th (n: INTEGER): detachable G
			-- What is the `i_th' item?
		require
			valid_n: not is_empty implies (1 |..| count).has (n)
		local
			i: INTEGER
		do
			from
				start
				i := 1
			until
				off or attached Result
			loop
				if i = n then
					Result := item_for_iteration
				end
				i := i + 1
				forth
			end
		ensure
			has_item: attached Result as al_result implies has_item (al_result)
		end

feature -- Basic Ops

	put_sorted, force_sorted (a_item: G; a_key: K)
			-- `put' or `force' and ensure `sort_asc'.
		require
			key_not_void_character: attached {CHARACTER} a_key implies a_key /= void_char
		do
			force (a_item, a_key)
			sort_asc
		end

	put_reverse_sorted, force_reverse_sorted (a_item: G; a_key: K)
			-- Either `put' or `force' into Current, but in reverse
			--	(`sort_desc') sorting order on items.
		require
			key_not_void_character: attached {CHARACTER} a_key implies a_key /= void_char
		do
			force (a_item, a_key)
			sort_desc
		end

	sorted: PART_SORTED_TWO_WAY_LIST [G]
			-- A sorted version of Current.
		do
			create Result.make_from_iterable (Current)
		end

	sorted_keys: PART_SORTED_TWO_WAY_LIST [PART_COMPARABLE]
			-- A sorted version of Current keys (rather than items).
		do
			create Result.make
			across
				keys.to_array as ic
			loop
				check keys_comparable: attached {PART_COMPARABLE} ic.item as al_key then
					Result.force (al_key)
				end
			end
		end

	sort_asc
			-- Do the `sort_asc' on a `sort' of `sorted', which
			--	is ascending by default.
		do
			sort (sorted, Sort_asc_signal)
		end

	sort_asc_keys
			-- Sort ascending on keys (rather than items).
		do
			sort_by_keys (sorted_keys, Sort_asc_signal)
		end

	sort_desc
			-- Do the `sort_desc' on `sort' of `sorted', which must
			--	be reversed and then sent on to `sort' for folding-in.
		do
			sort (sorted, Sort_desc_signal)
		end

	sort_desc_keys
			-- Sort descending on keys (rather than items).
		do
			sort_by_keys (sorted_keys, Sort_desc_signal)
		end

feature -- Output

	formatted_out: STRING
		do
			across
				Current as ic
			from
				create Result.make_empty
			loop
				Result.append_string_general (ic.item.out)
				Result.append_character (New_line_char)
			end
		end

	formatted_out_with_keys: STRING
		do
			from
				create Result.make_empty
				start
			until
				off
			loop
				check has_iteration_key: attached key_for_iteration as al_key then
					Result.append_string_general (al_key.out)
				end
				Result.append_character (Comma_char); Result.append_character (Space_char)
				Result.append_string_general (item_for_iteration.out)
				Result.append_character (New_line_char)
				forth
			end
		end

	json_out: STRING
			-- Compact JSON out.
		do
			Result := json_out_internal (Json_compact)
		end

	json_pretty_out: STRING
			-- Prettified JSON out.
			--	(WARNING: Not working ... yet!)
		do
			Result := json_out_internal (Json_pretty)
		end

feature {NONE} -- Implementation: Sorting

	sort (a_list: like sorted; a_reversed: BOOLEAN)
			-- Sort Current based on `a_list'.
		note
			design: "[
				The incoming `a_list' is already sorted by the items of the
				Current mapping. This routine folds in the keys of the mapping
				with the items in `a_list', which results in a new set of
				items that are in ascending/descending order based on the items.
				]"
			idea: "[
				It would also be possible to do a sorting based on a sort of the
				keys instead of the items. As it is, in HASH_TABLE, when one goes
				across-loop of the list, they are in natural-order--that is--they
				are in the order they were `put' or `forced' in. Therefore, when
				it comes to sorting, we have a choice. We can sort by items (which
				is what we're doing now) or we can sort by keys (the reason for
				this "idea" note).
				]"
		local
			l_current: like Current
			l_key: detachable K
			l_count: like count
		do
			l_current := Current.twin -- expensive
			check attached a_list then
				if a_reversed then
					across
						a_list.new_cursor.reversed as ic
					from
						wipe_out
					invariant
						count_advanced: l_count = count
					loop
						check has_key_for_item: attached key_for_item (ic.item, l_current) as al_key then
							l_key := al_key
						end
						check key_is_K: attached {K} l_key then
							force (ic.item, l_key)
						end
						l_count := l_count + 1
					end
				else
					across
						a_list as ic
					from
						wipe_out
					invariant
						count_advanced: l_count = count
					loop
						check has_key_for_item: attached key_for_item (ic.item, l_current) as al_key then
							l_key := al_key
						end
						check key_is_K: attached {K} l_key then
							force (ic.item, l_key)
						end
						l_count := l_count + 1
					end
				end
			end
		ensure
			all_accounted: count = old count
		end

	sort_by_keys (a_list: like sorted_keys; a_reversed: BOOLEAN)
		local
			l_current: like Current
		do
			if a_reversed then
				across
					a_list.new_cursor.reversed as ic_keys
				from
					l_current := Current.twin
					wipe_out
				loop
					check has_K_key: attached {K} ic_keys.item as al_key then
						if attached l_current.at (al_key) as al_item then
							force (al_item, al_key)
						end
					end
				end
			else
				across
					a_list as ic_keys
				from
					l_current := Current.twin
					wipe_out
				loop
					check has_K_key: attached {K} ic_keys.item as al_key then
						if attached l_current.at (al_key) as al_item then
							force (al_item, al_key)
						end
					end
				end
			end
		end

	key_for_item (a_item: G; a_list: like Current): detachable K
			-- Provide `key_for_item' of `a_item' from `a_list' (if any)
		note
			design_issue: "[
				QUESTION: Why is it that CHARACTER-based hashmap keys are a
							special-case in SORTED_HASH?
							
				ANSWER: Only in CHARACTER is Void an actual object reference.
				
				If you look at an ASC_II chart, you will see that NULL = 0h (0dec).
				Therefore, when you make an entity of type CHARACTER and set
				it to Void (Null), you are really setting it to 0 (%U) and not
				a Null or Void reference (e.g. not attached object). You can see
				this in action below in the "until".
				
				The "if-Boolean-expression" is there to test for the special-case
				that our Key is of type CHARACTER and we need to account for this
				fact.
				
				We test to see if the Result is attached (which is a stopping signal).
				In the case of CHARACTER, the default value of Result will be '%U',
				which is Void or Null as the 0-th character and not a "null-reference"
				like other data-types. Therefore, we need this extra test expression
				that first looks to see if the Result is data-typed as CHARACTER and
				then proceeds to assume that a valid Key is NOT a Null or Void!
				
				This leads to the following warning!
				]"
			WARNING: "DO NOT USE Void or Null CHARACTER AS A VALID KEY!"
		do
			from
				a_list.start
			until
				a_list.off or attached Result and then
					(if attached {CHARACTER} Result as al_result then
						Result /= '%U' else False
					end)
			loop
				if attached {G} a_list.item_for_iteration as al_item and then al_item ~ a_item then
					Result := a_list.key_for_iteration
				end
				a_list.forth
			end
		end

feature {NONE} -- Imp: Internal Output

	json_out_internal (a_prettified: BOOLEAN): STRING
		local
			l_conv: JSON_SERIALIZATION
			l_object: JSON_OBJECT
			l_array: JSON_ARRAY
			l_list: LIST [STRING]
		do
			l_conv := (create {JSON_SERIALIZATION_FACTORY}).smart_serialization

			if a_prettified then
				l_conv.set_pretty_printing
			else
				l_conv.set_compact_printing
			end

			create l_array.make (count)
			across
				formatted_out_with_keys.split (New_line_char) as ic_items
			loop
				if not ic_items.item.is_empty then
					create l_object.make_with_capacity (1)
					l_list := ic_items.item.split (',')
					l_object.put (create {JSON_STRING}.make_from_string (l_list [2]), create {JSON_STRING}.make_from_string (l_list [1]))
					l_array.add (l_object)
				end
			end

			create l_object.make_with_capacity (1)
			l_object.put (l_array, create {JSON_STRING}.make_from_string ("items"))
			Result := l_object.representation
		end

feature {NONE} -- Imp: Constants

	sort_asc_signal: BOOLEAN = False
	sort_desc_signal: BOOLEAN = True

	json_pretty: BOOLEAN = True
	json_compact: BOOLEAN = False

feature -- Constants

	comma_char: CHARACTER = ','
	space_char: CHARACTER = ' '
	new_line_char: CHARACTER = '%N'
	void_char: CHARACTER = '%U'

end
