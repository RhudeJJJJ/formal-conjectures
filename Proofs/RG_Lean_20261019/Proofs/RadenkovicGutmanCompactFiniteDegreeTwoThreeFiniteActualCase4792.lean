/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4792 : Family 10 := level10.get ⟨1112,by decide⟩
def sourceMap4792 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4792 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4792_checked : acceptsGraphIso
    (source (graph core4792) (root 10) 2 2) DegreeTwoThreeSpectrum7192.graph sourceMap4792=true := by decide +kernel
theorem fusedMap4792_checked : acceptsGraphIso
    (fused (graph core4792) (root 10) 2 2) DegreeTwoThreeSpectrum6210.graph fusedMap4792=true := by decide +kernel
theorem certified4792 : Certified (graph core4792) (root 10) 2 2 :=
  of_native_maps core4792 DegreeTwoThreeSpectrum7192.graph DegreeTwoThreeSpectrum6210.graph
    sourceMap4792 fusedMap4792 sourceMap4792_checked fusedMap4792_checked
    DegreeTwoThreeFiniteComparisons.comparison4792
#print axioms sourceMap4792_checked
#print axioms fusedMap4792_checked
#print axioms certified4792
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
