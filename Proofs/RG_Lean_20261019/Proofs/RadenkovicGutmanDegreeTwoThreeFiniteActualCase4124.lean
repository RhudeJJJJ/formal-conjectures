/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4124 : Family 8 := level8.get ⟨102,by decide⟩
def sourceMap4124 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4124 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4124_checked : acceptsGraphIso
    (source (graph core4124) (root 8) 2 2) DegreeTwoThreeSpectrum3106.graph sourceMap4124=true := by decide +kernel
theorem fusedMap4124_checked : acceptsGraphIso
    (fused (graph core4124) (root 8) 2 2) DegreeTwoThreeSpectrum2469.graph fusedMap4124=true := by decide +kernel
theorem certified4124 : Certified (graph core4124) (root 8) 2 2 :=
  of_native_maps core4124 DegreeTwoThreeSpectrum3106.graph DegreeTwoThreeSpectrum2469.graph
    sourceMap4124 fusedMap4124 sourceMap4124_checked fusedMap4124_checked
    DegreeTwoThreeFiniteComparisons.comparison4124
#print axioms sourceMap4124_checked
#print axioms fusedMap4124_checked
#print axioms certified4124
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
