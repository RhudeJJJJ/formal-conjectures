# Noch fehlende vollständige Lean-Beweise — 20. Oktober 2026

Alle erfassten PRs enthalten Lean-Aussagen. Diese Liste unterscheidet sie von vollständigen, öffentlichen Beweiszertifikaten. Grundlage sind die aktuellen PR-Dateien, ihre Platzhalter und die ausdrücklich dokumentierten Zertifikatsbereiche; nicht jedes ältere Zertifikat wurde in diesem Durchgang erneut im Kernel abgespielt.

Das neue Paket schließt 393a (#7380) sowie 379 und seine stärkere Fassung (#7379). Die vorhandenen Beweise für 393b/c bleiben erhalten. Danach verbleiben **19 offene PRs mit fehlenden vollständigen Beweisen oder Beweisteilen**:

| Beitrag | PR | Fehlender Bereich |
|---|---|---|
| Radenković–Gutman | [#7399](https://github.com/google-deepmind/formal-conjectures/pull/7399) | Universeller Pfadminimum- und Gleichheitssatz; Teilmodule vorhanden. |
| Spektralradius × Durchmesser | [#7402](https://github.com/google-deepmind/formal-conjectures/pull/7402) | Extremalschranke und Gleichheitsfälle. |
| Spektralradius × Radius | [#7401](https://github.com/google-deepmind/formal-conjectures/pull/7401) | Even-handle-Lemma und korrigierte Maxima; ursprüngliche Widerlegung bereits zertifiziert. |
| Energy–independence gap | [#7387](https://github.com/google-deepmind/formal-conjectures/pull/7387) | Universelle positive Konstante; Forschungsstatus ausdrücklich offen. |
| Chen Delta-Komplement | [#7382](https://github.com/google-deepmind/formal-conjectures/pull/7382) | Universelle Totaldominationsschranke. |
| Graphical Bell / Stirling | [#7385](https://github.com/google-deepmind/formal-conjectures/pull/7385) | Bell-Minimum und koeffizientenweiser Vergleich. |
| Kazemi Hypercube | [#7383](https://github.com/google-deepmind/formal-conjectures/pull/7383) | Universeller Satz zur Total-Dominator-Färbung. |
| Spektralradius minus chromatische Zahl | [#7386](https://github.com/google-deepmind/formal-conjectures/pull/7386) | Widerlegung des gedruckten Kandidaten, korrigiertes Maximum und Gleichheitsfälle. |
| Burghart M-Polynom | [#7397](https://github.com/google-deepmind/formal-conjectures/pull/7397) | Exakter Gegenbeweis mit dem definierten Polynom und Nichtisomorphie. |
| Grosdos Score-Determinante | [#7398](https://github.com/google-deepmind/formal-conjectures/pull/7398) | Zähler, Teilerfremdheit, Grad und höchster homogener Anteil. |
| Jia–Song Remoteness | [#7400](https://github.com/google-deepmind/formal-conjectures/pull/7400) | Ursprüngliche Widerlegung sowie korrigiertes Minimum und Eindeutigkeit. |
| Bound 44, eingeschränkte Bereiche | [#7396](https://github.com/google-deepmind/formal-conjectures/pull/7396) | Die drei universellen Varianten; keine globale Bound-44-Lösung behauptet. |
| AHZ Randić-Quotient | [#7395](https://github.com/google-deepmind/formal-conjectures/pull/7395) | Widerlegung und beide universellen Tadpole-Schwellenbereiche. |
| WOWII 376 | [#7378](https://github.com/google-deepmind/formal-conjectures/pull/7378) | Universelle Median-/Maximalgrad-Schranke. |
| WOWII 354, geschlossene Variante | [#7373](https://github.com/google-deepmind/formal-conjectures/pull/7373) | Open-Packing-Konstruktion und beide Folgerungen; historische offene Variante getrennt. |
| WOWII 361 | [#7377](https://github.com/google-deepmind/formal-conjectures/pull/7377) | Support-/Zentrum-Schranke und K2-Erweiterung. |
| WOWII 362 | [#7371](https://github.com/google-deepmind/formal-conjectures/pull/7371) | Radius- und Durchmesserschranke; Komponentenidentität bereits zertifiziert. |
| Erdős 64, Girth-six-Varianten | [#7404](https://github.com/google-deepmind/formal-conjectures/pull/7404) | Beide eingeschränkten universellen Sätze; Hauptproblem bleibt offen. |
| Byzov–Pushkarev | [#7403](https://github.com/google-deepmind/formal-conjectures/pull/7403) | Universeller Isomorphismus der tatsächlichen Automorphismengruppe. |

Zusätzlich sind die bereits ohne Übernahme geschlossenen PRs #7392 (nur die universellen Miss-Code-Obergrenzen; Konstruktionen und kleine Ordnungen sind bewiesen) und #7405 (Zeta-Varianten) formal unvollständig. Ihre Schließung betraf Aufnahmebereich und Quellenzuordnung; sie ist keine mathematische Widerlegung. Es wurde kein geschlossener PR neu eröffnet.

Bei RG, 362 und dem Radiusprodukt liegt eine Teilformalisierung vor. Beim Energy–independence gap ist zusätzlich die universelle mathematische Schließung nicht als gesichert ausgewiesen. Ein schriftlicher Beweis, ein grüner Statement-Build und ein Review sind jeweils von einem vollständigen Lean-Beweis zu unterscheiden. Private oder noch unveröffentlichte Dateien außerhalb dieser Fassungen werden durch diese Liste nicht ausgeschlossen.
