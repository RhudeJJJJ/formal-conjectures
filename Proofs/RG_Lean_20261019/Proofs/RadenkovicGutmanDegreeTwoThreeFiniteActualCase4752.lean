/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4752 : Family 10 := level10.get ⟨1006,by decide⟩
def sourceMap4752 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4752 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4752_checked : acceptsGraphIso
    (source (graph core4752) (root 10) 2 2) DegreeTwoThreeSpectrum7079.graph sourceMap4752=true := by decide +kernel
theorem fusedMap4752_checked : acceptsGraphIso
    (fused (graph core4752) (root 10) 2 2) DegreeTwoThreeSpectrum5990.graph fusedMap4752=true := by decide +kernel
theorem certified4752 : Certified (graph core4752) (root 10) 2 2 :=
  of_native_maps core4752 DegreeTwoThreeSpectrum7079.graph DegreeTwoThreeSpectrum5990.graph
    sourceMap4752 fusedMap4752 sourceMap4752_checked fusedMap4752_checked
    DegreeTwoThreeFiniteComparisons.comparison4752
#print axioms sourceMap4752_checked
#print axioms fusedMap4752_checked
#print axioms certified4752
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
