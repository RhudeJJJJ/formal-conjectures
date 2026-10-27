/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4714 : Family 10 := level10.get ⟨913,by decide⟩
def sourceMap4714 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4714 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4714_checked : acceptsGraphIso
    (source (graph core4714) (root 10) 2 2) DegreeTwoThreeSpectrum7497.graph sourceMap4714=true := by decide +kernel
theorem fusedMap4714_checked : acceptsGraphIso
    (fused (graph core4714) (root 10) 2 2) DegreeTwoThreeSpectrum5784.graph fusedMap4714=true := by decide +kernel
theorem certified4714 : Certified (graph core4714) (root 10) 2 2 :=
  of_native_maps core4714 DegreeTwoThreeSpectrum7497.graph DegreeTwoThreeSpectrum5784.graph
    sourceMap4714 fusedMap4714 sourceMap4714_checked fusedMap4714_checked
    DegreeTwoThreeFiniteComparisons.comparison4714
#print axioms sourceMap4714_checked
#print axioms fusedMap4714_checked
#print axioms certified4714
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
