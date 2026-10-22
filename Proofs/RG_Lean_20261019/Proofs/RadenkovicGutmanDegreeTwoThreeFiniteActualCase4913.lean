/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4913 : Family 10 := level10.get ⟨1394,by decide⟩
def sourceMap4913 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4913 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4913_checked : acceptsGraphIso
    (source (graph core4913) (root 10) 2 2) DegreeTwoThreeSpectrum7399.graph sourceMap4913=true := by decide +kernel
theorem fusedMap4913_checked : acceptsGraphIso
    (fused (graph core4913) (root 10) 2 2) DegreeTwoThreeSpectrum6760.graph fusedMap4913=true := by decide +kernel
theorem certified4913 : Certified (graph core4913) (root 10) 2 2 :=
  of_native_maps core4913 DegreeTwoThreeSpectrum7399.graph DegreeTwoThreeSpectrum6760.graph
    sourceMap4913 fusedMap4913 sourceMap4913_checked fusedMap4913_checked
    DegreeTwoThreeFiniteComparisons.comparison4913
#print axioms sourceMap4913_checked
#print axioms fusedMap4913_checked
#print axioms certified4913
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
