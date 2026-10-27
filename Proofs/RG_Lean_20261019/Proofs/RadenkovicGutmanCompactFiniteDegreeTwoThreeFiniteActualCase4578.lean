/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4578 : Family 10 := level10.get ⟨532,by decide⟩
def sourceMap4578 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4578 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4578_checked : acceptsGraphIso
    (source (graph core4578) (root 10) 2 2) DegreeTwoThreeSpectrum7141.graph sourceMap4578=true := by decide +kernel
theorem fusedMap4578_checked : acceptsGraphIso
    (fused (graph core4578) (root 10) 2 2) DegreeTwoThreeSpectrum5178.graph fusedMap4578=true := by decide +kernel
theorem certified4578 : Certified (graph core4578) (root 10) 2 2 :=
  of_native_maps core4578 DegreeTwoThreeSpectrum7141.graph DegreeTwoThreeSpectrum5178.graph
    sourceMap4578 fusedMap4578 sourceMap4578_checked fusedMap4578_checked
    DegreeTwoThreeFiniteComparisons.comparison4578
#print axioms sourceMap4578_checked
#print axioms fusedMap4578_checked
#print axioms certified4578
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
