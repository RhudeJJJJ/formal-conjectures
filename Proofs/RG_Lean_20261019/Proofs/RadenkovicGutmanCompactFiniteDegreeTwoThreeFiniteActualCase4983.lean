/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4983 : Family 10 := level10.get ⟨1579,by decide⟩
def sourceMap4983 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4983 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4983_checked : acceptsGraphIso
    (source (graph core4983) (root 10) 2 2) DegreeTwoThreeSpectrum7584.graph sourceMap4983=true := by decide +kernel
theorem fusedMap4983_checked : acceptsGraphIso
    (fused (graph core4983) (root 10) 2 2) DegreeTwoThreeSpectrum6062.graph fusedMap4983=true := by decide +kernel
theorem certified4983 : Certified (graph core4983) (root 10) 2 2 :=
  of_native_maps core4983 DegreeTwoThreeSpectrum7584.graph DegreeTwoThreeSpectrum6062.graph
    sourceMap4983 fusedMap4983 sourceMap4983_checked fusedMap4983_checked
    DegreeTwoThreeFiniteComparisons.comparison4983
#print axioms sourceMap4983_checked
#print axioms fusedMap4983_checked
#print axioms certified4983
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
