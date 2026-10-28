/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4900 : Family 10 := level10.get ⟨1371,by decide⟩
def sourceMap4900 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4900 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4900_checked : acceptsGraphIso
    (source (graph core4900) (root 10) 2 2) DegreeTwoThreeSpectrum7449.graph sourceMap4900=true := by decide +kernel
theorem fusedMap4900_checked : acceptsGraphIso
    (fused (graph core4900) (root 10) 2 2) DegreeTwoThreeSpectrum6714.graph fusedMap4900=true := by decide +kernel
theorem certified4900 : Certified (graph core4900) (root 10) 2 2 :=
  of_native_maps core4900 DegreeTwoThreeSpectrum7449.graph DegreeTwoThreeSpectrum6714.graph
    sourceMap4900 fusedMap4900 sourceMap4900_checked fusedMap4900_checked
    DegreeTwoThreeFiniteComparisons.comparison4900
#print axioms sourceMap4900_checked
#print axioms fusedMap4900_checked
#print axioms certified4900
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
