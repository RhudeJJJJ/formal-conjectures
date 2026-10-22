/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4797 : Family 10 := level10.get ⟨1123,by decide⟩
def sourceMap4797 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4797 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4797_checked : acceptsGraphIso
    (source (graph core4797) (root 10) 2 2) DegreeTwoThreeSpectrum7204.graph sourceMap4797=true := by decide +kernel
theorem fusedMap4797_checked : acceptsGraphIso
    (fused (graph core4797) (root 10) 2 2) DegreeTwoThreeSpectrum6232.graph fusedMap4797=true := by decide +kernel
theorem certified4797 : Certified (graph core4797) (root 10) 2 2 :=
  of_native_maps core4797 DegreeTwoThreeSpectrum7204.graph DegreeTwoThreeSpectrum6232.graph
    sourceMap4797 fusedMap4797 sourceMap4797_checked fusedMap4797_checked
    DegreeTwoThreeFiniteComparisons.comparison4797
#print axioms sourceMap4797_checked
#print axioms fusedMap4797_checked
#print axioms certified4797
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
