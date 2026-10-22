/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4617 : Family 10 := level10.get ⟨649,by decide⟩
def sourceMap4617 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4617 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4617_checked : acceptsGraphIso
    (source (graph core4617) (root 10) 2 2) DegreeTwoThreeSpectrum7299.graph sourceMap4617=true := by decide +kernel
theorem fusedMap4617_checked : acceptsGraphIso
    (fused (graph core4617) (root 10) 2 2) DegreeTwoThreeSpectrum5351.graph fusedMap4617=true := by decide +kernel
theorem certified4617 : Certified (graph core4617) (root 10) 2 2 :=
  of_native_maps core4617 DegreeTwoThreeSpectrum7299.graph DegreeTwoThreeSpectrum5351.graph
    sourceMap4617 fusedMap4617 sourceMap4617_checked fusedMap4617_checked
    DegreeTwoThreeFiniteComparisons.comparison4617
#print axioms sourceMap4617_checked
#print axioms fusedMap4617_checked
#print axioms certified4617
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
