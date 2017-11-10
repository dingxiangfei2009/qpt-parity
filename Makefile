CC=g++-7

all:
	$(CC) ordered.cc --std=c++17 -g -D_GLIBCXX_USE_CXX11_ABI=0 -o ordered

bad:
	$(CC) ordered.cc --std=c++17 -O2 -DBAD_UPDATE -o ordered

fast:
	$(CC) ordered.cc --std=c++17 -O2 -o ordered

fastrmcycle:
	$(CC) ordered.cc --std=c++17 -O2 -DREMOVE_CYCLES -o ordered

friedmann:
	$(CC) friedmann.cc -o friedmann -O2

weakgame:
	$(CC) weakgame.cc -o weakgame -O2

flip:
	$(CC) flip.cc -o flip -O2
