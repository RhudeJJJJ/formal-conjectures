/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4152 : Family 8 := level8.get ⟨173,by decide⟩
def sourceMap4152 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,7,8,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4152 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4152_checked : acceptsGraphIso
    (source (graph core4152) (root 8) 2 2) DegreeTwoThreeSpectrum3616.graph sourceMap4152=true := by decide +kernel
theorem fusedMap4152_checked : acceptsGraphIso
    (fused (graph core4152) (root 8) 2 2) DegreeTwoThreeSpectrum2884.graph fusedMap4152=true := by decide +kernel
theorem certified4152 : Certified (graph core4152) (root 8) 2 2 :=
  of_native_maps core4152 DegreeTwoThreeSpectrum3616.graph DegreeTwoThreeSpectrum2884.graph
    sourceMap4152 fusedMap4152 sourceMap4152_checked fusedMap4152_checked
    DegreeTwoThreeFiniteComparisons.comparison4152
#print axioms sourceMap4152_checked
#print axioms fusedMap4152_checked
#print axioms certified4152
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
