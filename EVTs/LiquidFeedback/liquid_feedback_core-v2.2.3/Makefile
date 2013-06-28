all:: lf_update lf_update_suggestion_order

lf_update: lf_update.c
	cc	-Wall -O2 \
		-I "`pg_config --includedir`" \
		-L "`pg_config --libdir`" \
		-o lf_update lf_update.c -lpq

lf_update_suggestion_order: lf_update_suggestion_order.c
	cc	-Wall -O2 \
		-I "`pg_config --includedir`" \
		-L "`pg_config --libdir`" \
		-o lf_update_suggestion_order lf_update_suggestion_order.c -lpq

clean::
	rm -f lf_update lf_update_suggestion_order
