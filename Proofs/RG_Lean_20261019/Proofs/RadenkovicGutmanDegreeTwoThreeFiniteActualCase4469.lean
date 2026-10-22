/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4469 : Family 10 := level10.get ⟨175,by decide⟩
def sourceMap4469 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4469 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4469_checked : acceptsGraphIso
    (source (graph core4469) (root 10) 2 2) DegreeTwoThreeSpectrum6816.graph sourceMap4469=true := by decide +kernel
theorem fusedMap4469_checked : acceptsGraphIso
    (fused (graph core4469) (root 10) 2 2) DegreeTwoThreeSpectrum5120.graph fusedMap4469=true := by decide +kernel
theorem certified4469 : Certified (graph core4469) (root 10) 2 2 :=
  of_native_maps core4469 DegreeTwoThreeSpectrum6816.graph DegreeTwoThreeSpectrum5120.graph
    sourceMap4469 fusedMap4469 sourceMap4469_checked fusedMap4469_checked
    DegreeTwoThreeFiniteComparisons.comparison4469
#print axioms sourceMap4469_checked
#print axioms fusedMap4469_checked
#print axioms certified4469
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
