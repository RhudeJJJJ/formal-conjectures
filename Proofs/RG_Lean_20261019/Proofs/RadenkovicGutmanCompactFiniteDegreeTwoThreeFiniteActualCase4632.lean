/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4632 : Family 10 := level10.get ⟨690,by decide⟩
def sourceMap4632 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4632 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4632_checked : acceptsGraphIso
    (source (graph core4632) (root 10) 2 2) DegreeTwoThreeSpectrum7338.graph sourceMap4632=true := by decide +kernel
theorem fusedMap4632_checked : acceptsGraphIso
    (fused (graph core4632) (root 10) 2 2) DegreeTwoThreeSpectrum5426.graph fusedMap4632=true := by decide +kernel
theorem certified4632 : Certified (graph core4632) (root 10) 2 2 :=
  of_native_maps core4632 DegreeTwoThreeSpectrum7338.graph DegreeTwoThreeSpectrum5426.graph
    sourceMap4632 fusedMap4632 sourceMap4632_checked fusedMap4632_checked
    DegreeTwoThreeFiniteComparisons.comparison4632
#print axioms sourceMap4632_checked
#print axioms fusedMap4632_checked
#print axioms certified4632
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
