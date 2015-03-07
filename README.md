SAMPL : Still Another Math Proof Library !
==========================================

Introduction
------------

This project aims to be the formalization of elementary mathematics in the COQ
proof assistant. I said "elementary" because I will try to formalize the content 
of my first math CPGE year. Of course, because of the huge lack of time in this
kind of study, it is likelly that a lot of content is missing. However, I will 
do my best to keep the whole project coherent :)
The architecture of the project (i.e. the mathematical content organisatioN) 
should be based on strong foundations. This means that I will try as much as
possible to be the least dependent possible to external librairies (such as the
stdlib). Of course, I don't want to reinvent the wheel, so it is likely that I 
grab a lot of basic content from these libraries, and rewrite it a bit to make
it coherent with the rest of the project. (Every authors' rights will be respected.)


Purpose
-------

I hope this project will help people trying to use COQ. It is very difficult for
students to use it well. I think (And this is what I personnally felt) it's even
more difficult than it is sorely lacking simple examples on the internet. 
I am far from an experienced user of COQ, so this repository may also be a way 
to show what I am doing, and to allow people to share better practices.
I also hope this project will introduce school courses in a different guise, and
maybe to deepen certain points formally (For me and for you).


Contributing
------------

Every contributions are welcome !
However, if you want to contribute, please let me know first. I would like every
(math) topics of this project be linked. Not really a content link, but a formal
link : everything should be based on other part of the project (unless it is a new
topic). But once again, please avoid adding content that exceeds the "level" of 
the rest of the project.

Installing
----------

The project comes with a linux shell script to generate the Makefile : (it uses
coq_makefile)
```
./build
```
If may launch make if nothing went wrong.

If you modified some files, you can rebuild the whole project with 
```
make -jX # Where X is the number of cores
```
If you added some files, you will have to edit the build script, and reprocess it.

The project use a custom version of coqdoc (available in the coqdoc/ directory) :
you have to build it first :
```
cd coqdoc
./build
cd ..
```
You can then generate the HTML documentation with :
```
make html
```

/!\ Documentation comment are only purposed for HTML documentation, because it uses
Mathjax /!\



License and rights
------------------

I licensed this project under GPL, even if I think it is more intented for 
learning purpose (Who knows ? Someone could find a real use of this stuff :p).
Cf the CONTRIBUTORS file, that list everybody that help or contribute to this 
project. For more informations about the GPL license, refer to the LICENSE file.
A really big part of the content I upload may be strongly inspired from my math 
courses. I am studying in the Chateaubriand high school in France, and every 
rights about this courses belongs to my math professor. 



Thanks for reading !
If you have any questions, or if you would like to contact me, please email :
	barnabe [dot] chauvin [at] gmail [dot] com
