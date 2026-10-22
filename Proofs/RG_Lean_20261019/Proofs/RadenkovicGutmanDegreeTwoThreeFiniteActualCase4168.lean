/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4168 : Family 8 := level8.get ⟨211,by decide⟩
def sourceMap4168 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4168 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4168_checked : acceptsGraphIso
    (source (graph core4168) (root 8) 2 2) DegreeTwoThreeSpectrum3792.graph sourceMap4168=true := by decide +kernel
theorem fusedMap4168_checked : acceptsGraphIso
    (fused (graph core4168) (root 8) 2 2) DegreeTwoThreeSpectrum2507.graph fusedMap4168=true := by decide +kernel
theorem certified4168 : Certified (graph core4168) (root 8) 2 2 :=
  of_native_maps core4168 DegreeTwoThreeSpectrum3792.graph DegreeTwoThreeSpectrum2507.graph
    sourceMap4168 fusedMap4168 sourceMap4168_checked fusedMap4168_checked
    DegreeTwoThreeFiniteComparisons.comparison4168
#print axioms sourceMap4168_checked
#print axioms fusedMap4168_checked
#print axioms certified4168
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
