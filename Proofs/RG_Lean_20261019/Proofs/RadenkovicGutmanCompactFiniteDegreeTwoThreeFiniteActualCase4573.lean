/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4573 : Family 10 := level10.get ⟨514,by decide⟩
def sourceMap4573 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4573 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4573_checked : acceptsGraphIso
    (source (graph core4573) (root 10) 2 2) DegreeTwoThreeSpectrum7107.graph sourceMap4573=true := by decide +kernel
theorem fusedMap4573_checked : acceptsGraphIso
    (fused (graph core4573) (root 10) 2 2) DegreeTwoThreeSpectrum5154.graph fusedMap4573=true := by decide +kernel
theorem certified4573 : Certified (graph core4573) (root 10) 2 2 :=
  of_native_maps core4573 DegreeTwoThreeSpectrum7107.graph DegreeTwoThreeSpectrum5154.graph
    sourceMap4573 fusedMap4573 sourceMap4573_checked fusedMap4573_checked
    DegreeTwoThreeFiniteComparisons.comparison4573
#print axioms sourceMap4573_checked
#print axioms fusedMap4573_checked
#print axioms certified4573
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
