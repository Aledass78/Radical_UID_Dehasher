#include <iostream>
#include <fstream>
#include <string>
#include <set>
#include <algorithm>

int main() {
    // Чтение слов из dictionary.txt в std::set
    std::ifstream dictFile("dictionary.txt");
    std::set<std::string> wordsSet;

    if (dictFile.is_open()) {
        std::string word;
        while (dictFile >> word) {
            wordsSet.insert(word);
        }
        dictFile.close();
    } else {
        std::cerr << "Can't open dictionary.txt" << std::endl;
        return 1;
    }

    // Чтение слов из add_to_dictionary.txt и добавление их в массив, если они отсутствуют
    std::ifstream addFile("add_to_dictionary.txt");

    if (addFile.is_open()) {
        std::string word;
        while (addFile >> word) {
            if (wordsSet.find(word) == wordsSet.end()) {
                wordsSet.insert(word);
            }
        }
        addFile.close();
    } else {
        std::cerr << "Can't open add_to_dictionary.txt" << std::endl;
        return 1;
    }

    // Запись массива обратно в dictionary.txt
    std::ofstream outFile("dictionary.txt");

    if (outFile.is_open()) {
        for (const auto& word : wordsSet) {
            outFile << word << std::endl;
        }
        outFile.close();
    } else {
        std::cerr << "Can't write to dictionary.txt" << std::endl;
        return 1;
    }

    std::cout << "Everything is allright." << std::endl;

    return 0;
}
