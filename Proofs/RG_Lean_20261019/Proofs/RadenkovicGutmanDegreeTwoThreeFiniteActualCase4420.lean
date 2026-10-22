/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4420 : Family 9 := level9.get ⟨650,by decide⟩
def sourceMap4420 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4420 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4420_checked : acceptsGraphIso
    (source (graph core4420) (root 9) 2 2) DegreeTwoThreeSpectrum4947.graph sourceMap4420=true := by decide +kernel
theorem fusedMap4420_checked : acceptsGraphIso
    (fused (graph core4420) (root 9) 2 2) DegreeTwoThreeSpectrum4439.graph fusedMap4420=true := by decide +kernel
theorem certified4420 : Certified (graph core4420) (root 9) 2 2 :=
  of_native_maps core4420 DegreeTwoThreeSpectrum4947.graph DegreeTwoThreeSpectrum4439.graph
    sourceMap4420 fusedMap4420 sourceMap4420_checked fusedMap4420_checked
    DegreeTwoThreeFiniteComparisons.comparison4420
#print axioms sourceMap4420_checked
#print axioms fusedMap4420_checked
#print axioms certified4420
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
