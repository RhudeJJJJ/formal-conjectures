/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4670 : Family 10 := level10.get ⟨797,by decide⟩
def sourceMap4670 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4670 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4670_checked : acceptsGraphIso
    (source (graph core4670) (root 10) 2 2) DegreeTwoThreeSpectrum7458.graph sourceMap4670=true := by decide +kernel
theorem fusedMap4670_checked : acceptsGraphIso
    (fused (graph core4670) (root 10) 2 2) DegreeTwoThreeSpectrum5586.graph fusedMap4670=true := by decide +kernel
theorem certified4670 : Certified (graph core4670) (root 10) 2 2 :=
  of_native_maps core4670 DegreeTwoThreeSpectrum7458.graph DegreeTwoThreeSpectrum5586.graph
    sourceMap4670 fusedMap4670 sourceMap4670_checked fusedMap4670_checked
    DegreeTwoThreeFiniteComparisons.comparison4670
#print axioms sourceMap4670_checked
#print axioms fusedMap4670_checked
#print axioms certified4670
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
