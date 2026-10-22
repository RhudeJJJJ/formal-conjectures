/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4633 : Family 10 := level10.get ⟨694,by decide⟩
def sourceMap4633 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4633 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4633_checked : acceptsGraphIso
    (source (graph core4633) (root 10) 2 2) DegreeTwoThreeSpectrum7346.graph sourceMap4633=true := by decide +kernel
theorem fusedMap4633_checked : acceptsGraphIso
    (fused (graph core4633) (root 10) 2 2) DegreeTwoThreeSpectrum5430.graph fusedMap4633=true := by decide +kernel
theorem certified4633 : Certified (graph core4633) (root 10) 2 2 :=
  of_native_maps core4633 DegreeTwoThreeSpectrum7346.graph DegreeTwoThreeSpectrum5430.graph
    sourceMap4633 fusedMap4633 sourceMap4633_checked fusedMap4633_checked
    DegreeTwoThreeFiniteComparisons.comparison4633
#print axioms sourceMap4633_checked
#print axioms fusedMap4633_checked
#print axioms certified4633
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
