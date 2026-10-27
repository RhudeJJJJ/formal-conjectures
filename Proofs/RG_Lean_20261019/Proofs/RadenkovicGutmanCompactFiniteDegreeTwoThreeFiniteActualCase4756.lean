/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4756 : Family 10 := level10.get ⟨1018,by decide⟩
def sourceMap4756 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4756 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4756_checked : acceptsGraphIso
    (source (graph core4756) (root 10) 2 2) DegreeTwoThreeSpectrum7094.graph sourceMap4756=true := by decide +kernel
theorem fusedMap4756_checked : acceptsGraphIso
    (fused (graph core4756) (root 10) 2 2) DegreeTwoThreeSpectrum6018.graph fusedMap4756=true := by decide +kernel
theorem certified4756 : Certified (graph core4756) (root 10) 2 2 :=
  of_native_maps core4756 DegreeTwoThreeSpectrum7094.graph DegreeTwoThreeSpectrum6018.graph
    sourceMap4756 fusedMap4756 sourceMap4756_checked fusedMap4756_checked
    DegreeTwoThreeFiniteComparisons.comparison4756
#print axioms sourceMap4756_checked
#print axioms fusedMap4756_checked
#print axioms certified4756
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
