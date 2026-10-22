/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3889 : Family 8 := level8.get ⟨190,by decide⟩
def sourceMap3889 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3889 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3889_checked : acceptsGraphIso
    (source (graph core3889) (root 8) 1 4) DegreeTwoThreeSpectrum4675.graph sourceMap3889=true := by decide +kernel
theorem fusedMap3889_checked : acceptsGraphIso
    (fused (graph core3889) (root 8) 1 4) DegreeTwoThreeSpectrum4179.graph fusedMap3889=true := by decide +kernel
theorem certified3889 : Certified (graph core3889) (root 8) 1 4 :=
  of_native_maps core3889 DegreeTwoThreeSpectrum4675.graph DegreeTwoThreeSpectrum4179.graph
    sourceMap3889 fusedMap3889 sourceMap3889_checked fusedMap3889_checked
    DegreeTwoThreeFiniteComparisons.comparison3889
#print axioms sourceMap3889_checked
#print axioms fusedMap3889_checked
#print axioms certified3889
def sourceMap3889swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3889swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3889swap_checked : acceptsGraphIso
    (source (graph core3889) (root 8) 4 1) DegreeTwoThreeSpectrum4675.graph sourceMap3889swap=true := by decide +kernel
theorem fusedMap3889swap_checked : acceptsGraphIso
    (fused (graph core3889) (root 8) 4 1) DegreeTwoThreeSpectrum4179.graph fusedMap3889swap=true := by decide +kernel
theorem certified3889swap : Certified (graph core3889) (root 8) 4 1 :=
  of_native_maps core3889 DegreeTwoThreeSpectrum4675.graph DegreeTwoThreeSpectrum4179.graph
    sourceMap3889swap fusedMap3889swap sourceMap3889swap_checked fusedMap3889swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3889
#print axioms sourceMap3889swap_checked
#print axioms fusedMap3889swap_checked
#print axioms certified3889swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
