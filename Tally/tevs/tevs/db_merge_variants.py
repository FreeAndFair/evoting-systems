import db
import pdb
import os
import os.path
import const
import time

drop_variants_table_str = "drop table if exists ocr_variants cascade;"

create_variants_table_str = """create table ocr_variants 
(id serial, 
standardized_id int default -1,
max_votes_in_contest int default 1, 
ocr_text varchar(80), 
orig_ocr_text varchar(80) default '');"""

populate_variants_table_contests_str = """insert into ocr_variants 
(ocr_text) 
select distinct substring(contest_text,1,80) as contest_text
from voteops order by contest_text"""

populate_variants_table_choices_str = """insert into ocr_variants 
(ocr_text,max_votes_in_contest) 
select distinct substring(choice_text,1,35) as choice_text, 0
from voteops order by choice_text;"""

update_variants_table_after_pop_str = """update ocr_variants set orig_ocr_text = ocr_text where True;"""

retrieve_variants_table_str = """select id, standardized_id, ocr_text, 
ocr_text as orig_ocr_text from ocr_variants"""

insert_a_into_variants_table_str = """insert into ocr_variants 
(id, standardized_id, ocr_text,orig_ocr_text) 
values (%s,%s,'%s','%s')"""

update_id_contests_str = """update voteops set contest_text_id = id, 
contest_text_standardized_id = standardized_id 
from ocr_variants 
where substring(orig_ocr_text,1,35)=substring(voteops.contest_text,1,35)"""

update_id_choices_str = """update voteops set choice_text_id = id, 
choice_text_standardized_id = standardized_id 
from ocr_variants 
where substring(orig_ocr_text,1,35) = substring(voteops.choice_text,1,35)"""

vote_count_query = """
select count(*) as votes, %s, cv.orig_ocr_text, chv.orig_ocr_text  
from ballots b join voteops v 
on b.ballot_id = v.ballot_id 
join ocr_variants cv 
on cv.id = v.contest_text_standardized_id 
join ocr_variants chv 
on chv.id = v.choice_text_standardized_id
where was_voted and not overvoted 
group by %s cv.orig_ocr_text, chv.orig_ocr_text 
order by %s cv.orig_ocr_text, chv.orig_ocr_text;
""" 

# for each standardized_contest_id, get distinct choices, assign serial numbers
# drop table temp_choices cascade; 
# create table temp_choices (id serial, choice_text varchar(80) default '');
# for n in standardized_contest_id_list:
#  insert into temp_choices from voteops where ocr_text_standardized_id = n; 
#  


def update_templates(associations,root):
    """change strings to standard forms in all templates"""
    # for a, use a[3] (original) not a[2] (cleaned)
    # perform replacements
    a_dict = {}
    for a in associations:
        standardized_id = a[1]
        orig_text = a[3]
        a_dict[standardized_id]=orig_text
    template_dir = "%s/templates" % (root,)
    templates = os.listdir(template_dir)
    for tname in ["%s/%s" % (template_dir,x) for x in templates]:
        # load template text
        #print tname
        t = open(tname,"r")
        out_t = open("%s.new" % (tname,),"w")
        for l in t.readlines():
            for a in associations:
                regular_id = a[0]
                standardized_id = a[1]
                orig_text = a[3]
                if l.find(orig_text)>-1:
                    s_text = a_dict[standardized_id]
                    l=l.replace(orig_text, s_text)
            out_t.write(l)
        t.close()
        out_t.close()
    try:
        unmerged_dir = "%s/unmerged_templates%d" % (root,int(time.time()))
        os.mkdir(unmerged_dir)
    except Exception, e:
        print "WARNING: unmerged_templates directory cannot be created."
    try:
        for tname in ["%s/%s" % (template_dir,x) for x in templates]:      
            if not tname.endswith(".new"):
                os.rename(tname,tname.replace(template_dir,unmerged_dir))
        for tname in ["%s/%s" % (template_dir,x) for x in templates]:      
            if tname.endswith(".new"):
                os.rename(tname,tname.replace(".new",""))
    except Exception, e:
        print "WARNING: altering templates requires write permission in the root directory %s" % (root,)
        print "WARNING: files in existing unmerged_templates under %s cannot be replaced" % (root,)
        print e
                          

def retrieve_ocr_variants_list(dbc):
    retval = dbc.query("select * from ocr_variants order by id")
    return retval

def create_ocr_variants_list(dbc):
    associations = []
    try:
        retval = dbc.query_no_returned_values(drop_variants_table_str)
        dbc.conn.commit()
    except Exception, e:
        pdb.set_trace()
        print e
    try:
        retval = dbc.query_no_returned_values(create_variants_table_str)
        dbc.conn.commit()
    except Exception, e:
        print e
    retval = dbc.query_no_returned_values(populate_variants_table_contests_str)
    dbc.conn.commit()
    retval = dbc.query_no_returned_values(populate_variants_table_choices_str)
    dbc.conn.commit()
    retval = dbc.query_no_returned_values(update_variants_table_after_pop_str)
    dbc.conn.commit()
    retval = dbc.query(retrieve_variants_table_str)

    for index1,x1 in enumerate(retval):
        # enable update of x1 fields, and store orig contest text (second x1[2])
        x1 = [x1[0],x1[1],x1[2],x1[2]]
        x1_associated = False
        for index2,x2 in enumerate(retval[index1+1:]):
            x2 = list(x2)
            # for these comparisons, eliminate leading / 
            while x1[2].startswith("/") or x1[2].startswith(" ") or x1[2].startswith("_"):
                x1[2] = x1[2][1:]
            while x2[2].startswith("/") or x2[2].startswith(" ") or x2[2].startswith("_"):
                x2[2] = x2[2][1:]
            # compare on shape, not meaning
            x1[2] = x1[2].replace("c","o").replace("e","o").replace("O","0").replace("l","1")
            x2[2] = x2[2].replace("c","o").replace("e","o").replace("O","0").replace("l","1")
            # if shifted one but otherwise dup'd in first 30, associate
            if x1[2][0:28] == x2[1:29] or x1[2][1:29]==x2[0:28]:
                #print x1[2],x2[2],"off by one"
                x1[1]=x2[0]
                x1_associated = True
            # if shifted two but otherwise dup'd in first 30, associate
            elif x1[2][0:28] == x2[2][2:30] or x1[2][2:30]==x2[2][0:28]: 
                #print x1[2],x2[2],"off by two"
                x1[1]=x2[0]
                x1_associated = True
            else:
                # if exactly matches on small, mostly on large, associate
                match_count, mismatch_count = 0,0
                words1 = x1[2][:35].replace("/"," / ").split(" ")
                words2 = x2[2][:35].replace("/"," / ").split(" ")
                # small words MUST match exactly
                # in the first thirty characters
                # to avoid combining lettered and numbered 
                # propositions, amendments, etc...
                for w1,w2 in zip(words1,words2):
                    if len(w1)>4 or len(w2)>4:
                        continue
                    # slashes sometimes read as I
                    if len(w1)==1 and len(w2)==1:
                        w1 = w1.replace("I","/")
                        w2 = w2.replace("I","/")
                    if w1 != w2:
                        #print w1,w2
                        mismatch_count += 100 # fail match
                # if the small words match exactly, see if there
                # are fewer mismatches than matches in the first thirty
                for c1,c2 in zip(x1[2][:35],x2[2][:35]):
                    if c1==c2: match_count += 1
                    else: mismatch_count += 1
                if match_count > (4*mismatch_count):
                    x1[1]=x2[0]
                    x1_associated = True
                    #print c1,c2,"4x more matches than mismatches"
        # if not otherwise associated, associate with yourself
        if not x1_associated:
            x1[1] = x1[0]
        associations.append(x1)
    update_templates(associations,const.root)
    return associations

def update_voteops_from_associations(dbc,associations):
    """ assoc"""
    # drop and recreate contest_variations from association list
    try:
        retval = dbc.query_no_returned_values(drop_variants_table_str)
        dbc.conn.commit()
    except Exception, e:
        pdb.set_trace()
        print e
    try:
        retval = dbc.query_no_returned_values(create_variants_table_str)
        dbc.conn.commit()
    except Exception, e:
        print e
    # populate variants table from associations
    try:
        print "Updating text variants table"
        for a in associations:
            dbc.query_no_returned_values(insert_a_into_variants_table_str % (a[0],a[1],a[2],a[3]))
        dbc.conn.commit()
    except Exception, e:
        print e
    # and update voteops
    try:
        dbc.conn.commit()
        print "Updating contest standard ids in voteops table"
        dbc.query_no_returned_values(update_id_contests_str)
        dbc.conn.commit()
        print "Updating choice standard ids in voteops table"
        dbc.query_no_returned_values(update_id_choices_str)
        dbc.conn.commit()

    except Exception, e:
        print e
