/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4460 : Family 10 := level10.get ⟨143,by decide⟩
def sourceMap4460 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4460 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4460_checked : acceptsGraphIso
    (source (graph core4460) (root 10) 2 2) DegreeTwoThreeSpectrum6812.graph sourceMap4460=true := by decide +kernel
theorem fusedMap4460_checked : acceptsGraphIso
    (fused (graph core4460) (root 10) 2 2) DegreeTwoThreeSpectrum5077.graph fusedMap4460=true := by decide +kernel
theorem certified4460 : Certified (graph core4460) (root 10) 2 2 :=
  of_native_maps core4460 DegreeTwoThreeSpectrum6812.graph DegreeTwoThreeSpectrum5077.graph
    sourceMap4460 fusedMap4460 sourceMap4460_checked fusedMap4460_checked
    DegreeTwoThreeFiniteComparisons.comparison4460
#print axioms sourceMap4460_checked
#print axioms fusedMap4460_checked
#print axioms certified4460
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
