/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4568 : Family 10 := level10.get ⟨492,by decide⟩
def sourceMap4568 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4568 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 2 2 v)
theorem sourceMap4568_checked : acceptsGraphIso
    (source (graph core4568) (root 10) 2 2) DegreeTwoThreeSpectrum6799.graph sourceMap4568=true := by decide +kernel
theorem fusedMap4568_checked : acceptsGraphIso
    (fused (graph core4568) (root 10) 2 2) DegreeTwoThreeSpectrum5957.graph fusedMap4568=true := by decide +kernel
theorem certified4568 : Certified (graph core4568) (root 10) 2 2 :=
  of_native_maps core4568 DegreeTwoThreeSpectrum6799.graph DegreeTwoThreeSpectrum5957.graph
    sourceMap4568 fusedMap4568 sourceMap4568_checked fusedMap4568_checked
    DegreeTwoThreeFiniteComparisons.comparison4568
#print axioms sourceMap4568_checked
#print axioms fusedMap4568_checked
#print axioms certified4568
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
