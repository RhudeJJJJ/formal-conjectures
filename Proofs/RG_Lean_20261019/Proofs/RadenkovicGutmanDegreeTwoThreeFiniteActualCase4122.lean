/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4122 : Family 8 := level8.get ⟨92,by decide⟩
def sourceMap4122 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,8,9,10,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4122 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4122_checked : acceptsGraphIso
    (source (graph core4122) (root 8) 2 2) DegreeTwoThreeSpectrum3614.graph sourceMap4122=true := by decide +kernel
theorem fusedMap4122_checked : acceptsGraphIso
    (fused (graph core4122) (root 8) 2 2) DegreeTwoThreeSpectrum2429.graph fusedMap4122=true := by decide +kernel
theorem certified4122 : Certified (graph core4122) (root 8) 2 2 :=
  of_native_maps core4122 DegreeTwoThreeSpectrum3614.graph DegreeTwoThreeSpectrum2429.graph
    sourceMap4122 fusedMap4122 sourceMap4122_checked fusedMap4122_checked
    DegreeTwoThreeFiniteComparisons.comparison4122
#print axioms sourceMap4122_checked
#print axioms fusedMap4122_checked
#print axioms certified4122
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
