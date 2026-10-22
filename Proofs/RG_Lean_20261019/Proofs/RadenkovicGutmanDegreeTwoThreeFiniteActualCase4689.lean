/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4689 : Family 10 := level10.get ⟨850,by decide⟩
def sourceMap4689 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4689 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4689_checked : acceptsGraphIso
    (source (graph core4689) (root 10) 2 2) DegreeTwoThreeSpectrum7504.graph sourceMap4689=true := by decide +kernel
theorem fusedMap4689_checked : acceptsGraphIso
    (fused (graph core4689) (root 10) 2 2) DegreeTwoThreeSpectrum5684.graph fusedMap4689=true := by decide +kernel
theorem certified4689 : Certified (graph core4689) (root 10) 2 2 :=
  of_native_maps core4689 DegreeTwoThreeSpectrum7504.graph DegreeTwoThreeSpectrum5684.graph
    sourceMap4689 fusedMap4689 sourceMap4689_checked fusedMap4689_checked
    DegreeTwoThreeFiniteComparisons.comparison4689
#print axioms sourceMap4689_checked
#print axioms fusedMap4689_checked
#print axioms certified4689
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
