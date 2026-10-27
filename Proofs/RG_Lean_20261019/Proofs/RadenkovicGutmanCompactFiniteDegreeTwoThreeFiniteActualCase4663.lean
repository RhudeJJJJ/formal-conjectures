/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4663 : Family 10 := level10.get ⟨782,by decide⟩
def sourceMap4663 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4663 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4663_checked : acceptsGraphIso
    (source (graph core4663) (root 10) 2 2) DegreeTwoThreeSpectrum7451.graph sourceMap4663=true := by decide +kernel
theorem fusedMap4663_checked : acceptsGraphIso
    (fused (graph core4663) (root 10) 2 2) DegreeTwoThreeSpectrum5563.graph fusedMap4663=true := by decide +kernel
theorem certified4663 : Certified (graph core4663) (root 10) 2 2 :=
  of_native_maps core4663 DegreeTwoThreeSpectrum7451.graph DegreeTwoThreeSpectrum5563.graph
    sourceMap4663 fusedMap4663 sourceMap4663_checked fusedMap4663_checked
    DegreeTwoThreeFiniteComparisons.comparison4663
#print axioms sourceMap4663_checked
#print axioms fusedMap4663_checked
#print axioms certified4663
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
