/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4458 : Family 10 := level10.get ⟨139,by decide⟩
def sourceMap4458 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4458 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4458_checked : acceptsGraphIso
    (source (graph core4458) (root 10) 2 2) DegreeTwoThreeSpectrum6848.graph sourceMap4458=true := by decide +kernel
theorem fusedMap4458_checked : acceptsGraphIso
    (fused (graph core4458) (root 10) 2 2) DegreeTwoThreeSpectrum5070.graph fusedMap4458=true := by decide +kernel
theorem certified4458 : Certified (graph core4458) (root 10) 2 2 :=
  of_native_maps core4458 DegreeTwoThreeSpectrum6848.graph DegreeTwoThreeSpectrum5070.graph
    sourceMap4458 fusedMap4458 sourceMap4458_checked fusedMap4458_checked
    DegreeTwoThreeFiniteComparisons.comparison4458
#print axioms sourceMap4458_checked
#print axioms fusedMap4458_checked
#print axioms certified4458
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
