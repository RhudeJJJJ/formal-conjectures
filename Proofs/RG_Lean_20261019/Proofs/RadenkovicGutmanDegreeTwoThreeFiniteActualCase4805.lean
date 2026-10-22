/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4805 : Family 10 := level10.get ⟨1143,by decide⟩
def sourceMap4805 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4805 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4805_checked : acceptsGraphIso
    (source (graph core4805) (root 10) 2 2) DegreeTwoThreeSpectrum7225.graph sourceMap4805=true := by decide +kernel
theorem fusedMap4805_checked : acceptsGraphIso
    (fused (graph core4805) (root 10) 2 2) DegreeTwoThreeSpectrum6273.graph fusedMap4805=true := by decide +kernel
theorem certified4805 : Certified (graph core4805) (root 10) 2 2 :=
  of_native_maps core4805 DegreeTwoThreeSpectrum7225.graph DegreeTwoThreeSpectrum6273.graph
    sourceMap4805 fusedMap4805 sourceMap4805_checked fusedMap4805_checked
    DegreeTwoThreeFiniteComparisons.comparison4805
#print axioms sourceMap4805_checked
#print axioms fusedMap4805_checked
#print axioms certified4805
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
