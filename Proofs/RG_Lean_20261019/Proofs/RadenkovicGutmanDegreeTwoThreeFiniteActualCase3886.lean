/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3886 : Family 8 := level8.get ⟨180,by decide⟩
def sourceMap3886 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3886 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3886_checked : acceptsGraphIso
    (source (graph core3886) (root 8) 1 4) DegreeTwoThreeSpectrum4632.graph sourceMap3886=true := by decide +kernel
theorem fusedMap3886_checked : acceptsGraphIso
    (fused (graph core3886) (root 8) 1 4) DegreeTwoThreeSpectrum4116.graph fusedMap3886=true := by decide +kernel
theorem certified3886 : Certified (graph core3886) (root 8) 1 4 :=
  of_native_maps core3886 DegreeTwoThreeSpectrum4632.graph DegreeTwoThreeSpectrum4116.graph
    sourceMap3886 fusedMap3886 sourceMap3886_checked fusedMap3886_checked
    DegreeTwoThreeFiniteComparisons.comparison3886
#print axioms sourceMap3886_checked
#print axioms fusedMap3886_checked
#print axioms certified3886
def sourceMap3886swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3886swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3886swap_checked : acceptsGraphIso
    (source (graph core3886) (root 8) 4 1) DegreeTwoThreeSpectrum4632.graph sourceMap3886swap=true := by decide +kernel
theorem fusedMap3886swap_checked : acceptsGraphIso
    (fused (graph core3886) (root 8) 4 1) DegreeTwoThreeSpectrum4116.graph fusedMap3886swap=true := by decide +kernel
theorem certified3886swap : Certified (graph core3886) (root 8) 4 1 :=
  of_native_maps core3886 DegreeTwoThreeSpectrum4632.graph DegreeTwoThreeSpectrum4116.graph
    sourceMap3886swap fusedMap3886swap sourceMap3886swap_checked fusedMap3886swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3886
#print axioms sourceMap3886swap_checked
#print axioms fusedMap3886swap_checked
#print axioms certified3886swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
