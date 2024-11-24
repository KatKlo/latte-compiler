# Kompilator języka Latte
Autor: Katarzyna Kloc (kk429317)

Repozytorium zawiera kompilator dla języka programowania Latte.

## Część pierwsza: Front-End

### Kompilacja i uruchamianie:

- `make`: Generuje plik wykonywalny `latc` w głównym katalogu repozytorium oraz usuwa zbędne pliki powstałe w trakcie procesu kompilacji.
- `make clean`: Usuwa wszystkie zbędne pliki powstałe w procesie kompilacji.
- `make distclean`: Usuwa wszystkie pliki wygenerowane podczas procesu kompilacji (w tym plik wykonywalny).

### Zakres funkcjonalności:

Kompilator obsługuje bazową wersję języka Latte rozszerzoną o tablice (i pętle `foreach`).

### Działanie:

Na wejściu kompilator otrzymuje plik z kodem źródłowym w języku Latte. Wszelkie błędy są przekierowywane do standardowego strumienia błędów:
- W pierwszym wierszu wyświetlany jest status `OK` (jeżeli kod jest poprawny) lub `ERROR`.
- W kolejnych liniach wyświetlane są ostrzeżenia dla poprawnie analizowanego kodu lub pierwszy napotkany błąd.

Charakterystyka działania kompilatora:
- Wykrywanie błędów składniowych
- Wykrywanie błędów statycznych, między innymi takich jak: niezgodność typów, brak funkcji `main` czy użycie niezadeklarowanych zmiennych
- Ignorowanie błędów typu "Runtime", na przykład: niejawne dzielenie przez zero czy przekroczenie zakresu typu podczas operacji
- Generowanie ostrzeżeń związanych z nieosiągalnymi instrukcjami i jawnie nieskończonymi pętlami

### Implementacja kompilatora:

Kompilator został zrealizowany przy użyciu języka Haskell, wykorzystując monady Writer, State, Reader oraz Except.

Sposób implementacji został zainspirowany poprzez moje własne rozwiązania do zadania interpretera dla JPP i kompilatora języka Instant dla tego kursu. Analizy leksykalna i składniowa są generowane przy użyciu narzędzia [bnfc](https://bnfc.digitalgrammars.com) na podstawie dostarczonego pliku `Latte.cf`.

### Struktura projektu:

- `src/Grammar/`: Zawiera pliki wygenerowane za pomocą [bnfc](https://bnfc.digitalgrammars.com) oraz plik `Latte.cf`.
- `src/`: Zawiera pliki źródłowe kompilatora.