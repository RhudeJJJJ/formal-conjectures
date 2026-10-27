/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4072 : Family 7 := level7.get ⟨47,by decide⟩
def sourceMap4072 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4072 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4072_checked : acceptsGraphIso
    (source (graph core4072) (root 7) 2 2) DegreeTwoThreeSpectrum2161.graph sourceMap4072=true := by decide +kernel
theorem fusedMap4072_checked : acceptsGraphIso
    (fused (graph core4072) (root 7) 2 2) DegreeTwoThreeSpectrum1839.graph fusedMap4072=true := by decide +kernel
theorem certified4072 : Certified (graph core4072) (root 7) 2 2 :=
  of_native_maps core4072 DegreeTwoThreeSpectrum2161.graph DegreeTwoThreeSpectrum1839.graph
    sourceMap4072 fusedMap4072 sourceMap4072_checked fusedMap4072_checked
    DegreeTwoThreeFiniteComparisons.comparison4072
#print axioms sourceMap4072_checked
#print axioms fusedMap4072_checked
#print axioms certified4072
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
