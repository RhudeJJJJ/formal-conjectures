/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4875 : Family 10 := level10.get ⟨1313,by decide⟩
def sourceMap4875 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4875 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4875_checked : acceptsGraphIso
    (source (graph core4875) (root 10) 2 2) DegreeTwoThreeSpectrum7394.graph sourceMap4875=true := by decide +kernel
theorem fusedMap4875_checked : acceptsGraphIso
    (fused (graph core4875) (root 10) 2 2) DegreeTwoThreeSpectrum6613.graph fusedMap4875=true := by decide +kernel
theorem certified4875 : Certified (graph core4875) (root 10) 2 2 :=
  of_native_maps core4875 DegreeTwoThreeSpectrum7394.graph DegreeTwoThreeSpectrum6613.graph
    sourceMap4875 fusedMap4875 sourceMap4875_checked fusedMap4875_checked
    DegreeTwoThreeFiniteComparisons.comparison4875
#print axioms sourceMap4875_checked
#print axioms fusedMap4875_checked
#print axioms certified4875
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
