run: compile
	./src/Main

compile:
	agda -c src/Main.agda

clean:
	rm ./src/Main
	rm -r ./src/**.agdai
	rm -r ./src/MAlonzo
