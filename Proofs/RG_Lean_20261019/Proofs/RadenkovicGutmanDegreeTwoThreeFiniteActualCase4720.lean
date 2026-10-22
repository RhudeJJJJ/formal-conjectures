/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4720 : Family 10 := level10.get ⟨930,by decide⟩
def sourceMap4720 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4720 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4720_checked : acceptsGraphIso
    (source (graph core4720) (root 10) 2 2) DegreeTwoThreeSpectrum7545.graph sourceMap4720=true := by decide +kernel
theorem fusedMap4720_checked : acceptsGraphIso
    (fused (graph core4720) (root 10) 2 2) DegreeTwoThreeSpectrum5824.graph fusedMap4720=true := by decide +kernel
theorem certified4720 : Certified (graph core4720) (root 10) 2 2 :=
  of_native_maps core4720 DegreeTwoThreeSpectrum7545.graph DegreeTwoThreeSpectrum5824.graph
    sourceMap4720 fusedMap4720 sourceMap4720_checked fusedMap4720_checked
    DegreeTwoThreeFiniteComparisons.comparison4720
#print axioms sourceMap4720_checked
#print axioms fusedMap4720_checked
#print axioms certified4720
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
