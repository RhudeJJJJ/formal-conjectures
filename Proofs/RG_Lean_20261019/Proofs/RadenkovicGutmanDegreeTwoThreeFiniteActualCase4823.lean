/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4823 : Family 10 := level10.get ⟨1191,by decide⟩
def sourceMap4823 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4823 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4823_checked : acceptsGraphIso
    (source (graph core4823) (root 10) 2 2) DegreeTwoThreeSpectrum7280.graph sourceMap4823=true := by decide +kernel
theorem fusedMap4823_checked : acceptsGraphIso
    (fused (graph core4823) (root 10) 2 2) DegreeTwoThreeSpectrum6363.graph fusedMap4823=true := by decide +kernel
theorem certified4823 : Certified (graph core4823) (root 10) 2 2 :=
  of_native_maps core4823 DegreeTwoThreeSpectrum7280.graph DegreeTwoThreeSpectrum6363.graph
    sourceMap4823 fusedMap4823 sourceMap4823_checked fusedMap4823_checked
    DegreeTwoThreeFiniteComparisons.comparison4823
#print axioms sourceMap4823_checked
#print axioms fusedMap4823_checked
#print axioms certified4823
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
