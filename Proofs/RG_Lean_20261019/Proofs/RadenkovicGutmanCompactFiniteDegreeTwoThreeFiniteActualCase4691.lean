/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4691 : Family 10 := level10.get ⟨857,by decide⟩
def sourceMap4691 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4691 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4691_checked : acceptsGraphIso
    (source (graph core4691) (root 10) 2 2) DegreeTwoThreeSpectrum7531.graph sourceMap4691=true := by decide +kernel
theorem fusedMap4691_checked : acceptsGraphIso
    (fused (graph core4691) (root 10) 2 2) DegreeTwoThreeSpectrum5693.graph fusedMap4691=true := by decide +kernel
theorem certified4691 : Certified (graph core4691) (root 10) 2 2 :=
  of_native_maps core4691 DegreeTwoThreeSpectrum7531.graph DegreeTwoThreeSpectrum5693.graph
    sourceMap4691 fusedMap4691 sourceMap4691_checked fusedMap4691_checked
    DegreeTwoThreeFiniteComparisons.comparison4691
#print axioms sourceMap4691_checked
#print axioms fusedMap4691_checked
#print axioms certified4691
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
