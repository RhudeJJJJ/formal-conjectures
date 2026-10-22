/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1857 : Family 10 := level10.get ⟨1274,by decide⟩
def sourceMap1857 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1857 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1857_checked : acceptsGraphIso
    (source (graph core1857) (root 10) 0 2) DegreeTwoThreeSpectrum3427.graph sourceMap1857=true := by decide +kernel
theorem fusedMap1857_checked : acceptsGraphIso
    (fused (graph core1857) (root 10) 0 2) DegreeTwoThreeSpectrum3428.graph fusedMap1857=true := by decide +kernel
theorem certified1857 : Certified (graph core1857) (root 10) 0 2 :=
  of_native_maps core1857 DegreeTwoThreeSpectrum3427.graph DegreeTwoThreeSpectrum3428.graph
    sourceMap1857 fusedMap1857 sourceMap1857_checked fusedMap1857_checked
    DegreeTwoThreeFiniteComparisons.comparison1857
#print axioms sourceMap1857_checked
#print axioms fusedMap1857_checked
#print axioms certified1857
def sourceMap1857swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1857swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1857swap_checked : acceptsGraphIso
    (source (graph core1857) (root 10) 2 0) DegreeTwoThreeSpectrum3427.graph sourceMap1857swap=true := by decide +kernel
theorem fusedMap1857swap_checked : acceptsGraphIso
    (fused (graph core1857) (root 10) 2 0) DegreeTwoThreeSpectrum3428.graph fusedMap1857swap=true := by decide +kernel
theorem certified1857swap : Certified (graph core1857) (root 10) 2 0 :=
  of_native_maps core1857 DegreeTwoThreeSpectrum3427.graph DegreeTwoThreeSpectrum3428.graph
    sourceMap1857swap fusedMap1857swap sourceMap1857swap_checked fusedMap1857swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1857
#print axioms sourceMap1857swap_checked
#print axioms fusedMap1857swap_checked
#print axioms certified1857swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
