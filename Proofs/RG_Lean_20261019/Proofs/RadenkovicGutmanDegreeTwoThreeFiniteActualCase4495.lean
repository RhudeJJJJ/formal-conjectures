/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4495 : Family 10 := level10.get ⟨270,by decide⟩
def sourceMap4495 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4495 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4495_checked : acceptsGraphIso
    (source (graph core4495) (root 10) 2 2) DegreeTwoThreeSpectrum6449.graph sourceMap4495=true := by decide +kernel
theorem fusedMap4495_checked : acceptsGraphIso
    (fused (graph core4495) (root 10) 2 2) DegreeTwoThreeSpectrum5394.graph fusedMap4495=true := by decide +kernel
theorem certified4495 : Certified (graph core4495) (root 10) 2 2 :=
  of_native_maps core4495 DegreeTwoThreeSpectrum6449.graph DegreeTwoThreeSpectrum5394.graph
    sourceMap4495 fusedMap4495 sourceMap4495_checked fusedMap4495_checked
    DegreeTwoThreeFiniteComparisons.comparison4495
#print axioms sourceMap4495_checked
#print axioms fusedMap4495_checked
#print axioms certified4495
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
