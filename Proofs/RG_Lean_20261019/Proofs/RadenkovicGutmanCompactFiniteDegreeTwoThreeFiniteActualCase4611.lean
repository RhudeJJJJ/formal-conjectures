/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4611 : Family 10 := level10.get ⟨635,by decide⟩
def sourceMap4611 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4611 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4611_checked : acceptsGraphIso
    (source (graph core4611) (root 10) 2 2) DegreeTwoThreeSpectrum7293.graph sourceMap4611=true := by decide +kernel
theorem fusedMap4611_checked : acceptsGraphIso
    (fused (graph core4611) (root 10) 2 2) DegreeTwoThreeSpectrum5329.graph fusedMap4611=true := by decide +kernel
theorem certified4611 : Certified (graph core4611) (root 10) 2 2 :=
  of_native_maps core4611 DegreeTwoThreeSpectrum7293.graph DegreeTwoThreeSpectrum5329.graph
    sourceMap4611 fusedMap4611 sourceMap4611_checked fusedMap4611_checked
    DegreeTwoThreeFiniteComparisons.comparison4611
#print axioms sourceMap4611_checked
#print axioms fusedMap4611_checked
#print axioms certified4611
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
