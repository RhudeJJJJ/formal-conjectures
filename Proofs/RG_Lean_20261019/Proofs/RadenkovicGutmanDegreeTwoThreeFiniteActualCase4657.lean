/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4657 : Family 10 := level10.get ⟨760,by decide⟩
def sourceMap4657 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4657 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4657_checked : acceptsGraphIso
    (source (graph core4657) (root 10) 2 2) DegreeTwoThreeSpectrum7419.graph sourceMap4657=true := by decide +kernel
theorem fusedMap4657_checked : acceptsGraphIso
    (fused (graph core4657) (root 10) 2 2) DegreeTwoThreeSpectrum5530.graph fusedMap4657=true := by decide +kernel
theorem certified4657 : Certified (graph core4657) (root 10) 2 2 :=
  of_native_maps core4657 DegreeTwoThreeSpectrum7419.graph DegreeTwoThreeSpectrum5530.graph
    sourceMap4657 fusedMap4657 sourceMap4657_checked fusedMap4657_checked
    DegreeTwoThreeFiniteComparisons.comparison4657
#print axioms sourceMap4657_checked
#print axioms fusedMap4657_checked
#print axioms certified4657
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
