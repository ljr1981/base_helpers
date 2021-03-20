note
	description: "[
		Eiffel tests that can be executed by testing tool.
	]"
	testing: "type/manual"

class
	SORTED_HASH_TEST_SET

inherit
	TEST_SET_SUPPORT

feature -- Test routines

	sorted_hash_with_character_keys_tests
			-- Special-case of keys are CHARACTER
		note
			heads_up: "[
				QUESTION: Why is it that CHARACTER-based hashmap keys are a
							special-case in SORTED_HASH?
							
				ANSWER: Only in CHARACTER is Void an actual object reference.
				
				If you look at an ASC_II chart, you will see that NULL = 0h (0dec).
				Therefore, when you make an entity of type CHARACTER and set
				it to Void (Null), you are really setting it to 0 (%U) and not
				a Null or Void reference (e.g. not attached object). You can see
				this in action in {SORTED_HASH}.key_for_item in the "until" part.
				]"
			testing:
				"covers/{HASH_TABLE_ITERATION_CURSOR}.item",
				"covers/{ITERATION_CURSOR}.after",
				"covers/{ITERATION_CURSOR}.forth",
				"covers/{SORTED_HASH}.count",
				"covers/{SORTED_HASH}.formatted_out",
				"covers/{SORTED_HASH}.formatted_out_with_keys",
				"covers/{SORTED_HASH}.i_th",
				"covers/{SORTED_HASH}.make",
				"covers/{SORTED_HASH}.new_cursor",
				"covers/{SORTED_HASH}.put_sorted",
				"covers/{SORTED_HASH}.sort_desc",
				"covers/{STRING_8}.plus",
				"execution/isolated"
		local
			l_hash: SORTED_HASH [STRING, STRING]
		do
			create l_hash.make (2)
			l_hash.put_sorted ("zebra", "Y")
			l_hash.put_sorted ("anaconda", "X")

			print ("ascending order%N")
			across l_hash as ic loop print (ic.item + "%N") end

			assert_integers_equal ("count_two_1", 2, l_hash.count)
			if attached l_hash.i_th (1) as al_item then
				assert_strings_equal ("1_1", "anaconda", al_item)
			end
			if attached l_hash.i_th (2) as al_item then
				assert_strings_equal ("1_2", "zebra", al_item)
			end
			assert_strings_equal ("asc_list", "anaconda%Nzebra%N", l_hash.formatted_out)

			l_hash.sort_desc
			print ("descending order%N")
			across l_hash as ic loop print (ic.item + "%N") end

			assert_integers_equal ("count_two_2", 2, l_hash.count)
			if attached l_hash.i_th (1) as al_item then
				assert_strings_equal ("2_1", "zebra", al_item)
			end
			if attached l_hash.i_th (2) as al_item then
				assert_strings_equal ("2_2", "anaconda", al_item)
			end
			assert_strings_equal ("desc_list", "zebra%Nanaconda%N", l_hash.formatted_out)
			assert_strings_equal ("desc_formatted_out_with_keys", desc_formatted_out_with_keys, l_hash.formatted_out_with_keys)
		end

	json_out_tests
		local
			l_hash: SORTED_HASH [STRING, STRING]
		do
			create l_hash.make (2)
			l_hash.put_sorted ("zebra", "Y")
			l_hash.put_sorted ("anaconda", "X")
			assert_strings_equal ("json_out_result", json_out_result, l_hash.json_out)
			assert_strings_equal ("json_pretty_out_result", json_pretty_out_result, l_hash.json_pretty_out)
		end

feature {NONE} -- Test Support

	desc_formatted_out_with_keys: STRING = "[
Y, zebra
X, anaconda

]"

	json_out_result: STRING = "[
{"items":[{"X":" anaconda"},{"Y":" zebra"}]}
]"

	json_pretty_out_result: STRING = "[
{"items":[{"X":" anaconda"},{"Y":" zebra"}]}
]"

end


